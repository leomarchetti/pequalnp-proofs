"""Wave racer for plain Represents FIND steps (k <= 5): send a checked circuit within a minute of a step appearing.

Loop: read gaps.json every POLL s. Steps it has not seen before go to WSL as one batch: SAT, AND/OR/NOT, BUDGET1 s
each, 8 at a time, results streamed back. For each SAT result the circuit is verified in Python, and the desk is asked
about the step right before sending:
  - open or leased: send;
  - pr_open: send only while every competing PR is younger than RACE_WINDOW s;
  - anything else: skip.
Send means one Lean file on a branch named after the step, cut from upstream main in the ../pnp-race worktree, pushed
to the fork, then one PR at least GAP s after the last. Each step is sent at most once (state.json), so we never
re-send to a closed step. Steps the first pass leaves UNKNOWN get one longer pass (BUDGET2) when no new steps wait.
Steps already open when the racer first starts are recorded as 'old' and skipped.
The racer exits on a STOP notice on upstream main, on a 429 from the desk, or on a GitHub rate-limit answer.
usage: python -I -X utf8 -u .pnp/race/wave_racer.py [--selftest]
"""
import json, os, re, subprocess, sys, time, threading, urllib.request, urllib.parse
from datetime import datetime, timezone

ROOT = os.environ.get('PNP_ROOT', os.getcwd())  # the proofs checkout
WT = os.environ.get('PNP_RACE_WT', os.path.join(os.path.dirname(ROOT), 'pnp-race'))  # a spare worktree
DIR = ROOT + '/.pnp/race'
WSL_DIR = os.environ['PNP_RACE_WSL_DIR']  # DIR as WSL sees it, e.g. /mnt/c/.../.pnp/race
UP = 'open-goat/pequalnp-proofs'
UP_URL = 'https://github.com/%s.git' % UP
ME = os.environ['PNP_GH']  # your GitHub login (the fork's owner)
SNAP = 'https://data.pequalnp.com/data/desk/gaps.json'
DESK = 'https://pequalnp.com/desk'
POLL, BUDGET1, BUDGET2, RACE_WINDOW, GAP = 20, 20, 150, 45, 3
PAT = re.compile(r'^∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ '
                 r'PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C$')

def say(*a):
    line = datetime.now().strftime('%H:%M:%S ') + ' '.join(str(x) for x in a)
    print(line, flush=True)
    with open(DIR + '/race.log', 'a', encoding='utf-8') as f: f.write(line + '\n')

def load_state():
    try: return json.load(open(DIR + '/state.json', encoding='utf-8'))
    except FileNotFoundError: return {}

def save_state(st):
    tmp = DIR + '/state.json.tmp'
    json.dump(st, open(tmp, 'w', encoding='utf-8'), indent=0, sort_keys=True)
    os.replace(tmp, DIR + '/state.json')

def snapshot():
    """{id: (k, s, mask, weight, gap)} for open plain Represents steps with k <= 5"""
    req = urllib.request.Request(SNAP, headers={'User-Agent': 'curl/8.0', 'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(req, timeout=40) as r:
        G = json.load(r)['gaps']
    out = {}
    for g in G:
        m = PAT.match((g.get('statement') or '').strip())
        if not m or m.group(2) != m.group(4) or int(m.group(2)) > 5 or g.get('dead'): continue
        out[g['id']] = (int(m.group(2)), int(m.group(1)), int(m.group(3)), int(g.get('weight') or 0), g)
    return out

def ok(k, mask, gates, s):
    n = 2 * k; out = n + len(gates) - 1
    if not gates or len(gates) > s: return False
    for o, a, b in gates:
        if o not in (0, 1, 2): return False
    for j, (o, a, b) in enumerate(gates):
        if not (0 <= a < n + j) or (o != 2 and not (0 <= b < n + j)): return False
    for u in range(k):
        for v in range(k):
            w = [i == u for i in range(k)] + [j == v for j in range(k)]
            for o, a, b in gates:
                w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
            if w[out] != bool((mask >> (k * u + v)) & 1): return False
    return True

def lean_file(gid, k, gates, g):
    """the whole proof file: the step's imports, the witness in a helper namespace, the theorem with the step's statement"""
    name = 'PEqualNP.Outside.' + gid.replace('-', '_')
    ns = name + '.Helpers'
    ops = {0: 'and', 1: 'or', 2: 'not'}
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
    imports = g.get('imports') or ['PEqualNP.Defs']
    return (''.join('import %s\n' % i for i in imports) + '\n'
            f'namespace {ns}\n\nopen PEqualNP.CircuitLowerBounds\n\n'
            f'/-- A {len(gates)}-gate circuit found by SAT-based exact synthesis: inputs 0..{k-1} are the left vertex,\n'
            f'{k}..{2*k-1} the right vertex, gate `j` writes wire `{2*k} + j`, the output is the last gate. -/\n'
            f'def witness : Circuit :=\n  ⟨[{gl}], {2*k + len(gates) - 1}⟩\n\nend {ns}\n\n'
            f'theorem {name} : {g["statement"].strip()} := by\n'
            f'  refine ⟨{ns}.witness, ?_, by decide, by decide +kernel⟩\n'
            f'  simp [PEqualNP.MetaComplexity.FanInTwo, {ns}.witness]\n')

def run(args, cwd=WT, timeout=120):
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=timeout)
    return r.returncode, (r.stdout + r.stderr).strip()

class Stop(Exception): pass

def desk_state(gid):
    url = DESK + '/step?' + urllib.parse.urlencode({'gap': gid})
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers={'User-Agent': 'curl/8.0'}), timeout=10) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        if e.code == 429: raise Stop('desk answered 429')
        try: return json.load(e)
        except Exception: return {}
    except Exception:
        return {}

def pr_age(num):
    rc, out = run(['gh', 'pr', 'view', str(num), '-R', UP, '--json', 'createdAt', '--jq', '.createdAt'], cwd=ROOT, timeout=30)
    try: return time.time() - datetime.strptime(out.strip()[:20], '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=timezone.utc).timestamp()
    except Exception: return 1e9

class Sender:
    def __init__(self):
        self.last = 0.0; self.fetched = 0.0; self.lock = threading.Lock()

    def fetch(self):
        with self.lock:
            if time.time() - self.fetched < 60: return
            rc, out = run(['git', 'fetch', '-q', UP_URL, 'main'], timeout=90)
            if rc: say('fetch failed:', out[:200]); return
            if run(['git', 'cat-file', '-e', 'FETCH_HEAD:STOP'])[0] == 0: raise Stop('STOP notice on upstream main')
            self.fetched = time.time()

    def send(self, gid, k, s, gates, g, st):
        d = desk_state(gid)
        state = d.get('state')
        if state in ('open', 'leased') or state is None:
            why = 'desk: %s' % (state or 'no answer')
        elif state == 'pr_open':
            ages = [pr_age(p) for p in (d.get('prs') or [])]
            if ages and max(ages) > RACE_WINDOW:
                st[gid] = 'late'; say(gid, 'late: competing PR(s) %s, oldest %.0f s' % (d.get('prs'), max(ages))); return
            why = 'racing PR(s) %s, oldest %.0f s' % (d.get('prs'), max(ages) if ages else 0)
        else:
            st[gid] = 'closed:' + str(state); say(gid, 'not sent, desk state', state); return
        self.fetch()
        path = g.get('file') or 'lean/PEqualNP/Outside/%s.lean' % gid.replace('-', '_')
        if run(['git', 'cat-file', '-e', 'FETCH_HEAD:' + path])[0] == 0:
            st[gid] = 'on_main'; say(gid, 'already on main'); return
        rc, out = run(['git', 'checkout', '-q', '-f', '-B', gid, 'FETCH_HEAD'])
        if rc: say(gid, 'checkout failed', out[:200]); st[gid] = 'error'; return
        with open(WT + '/' + path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(lean_file(gid, k, gates, g))
        run(['git', 'add', path])
        rc, out = run(['git', 'commit', '-q', '-m', gid + '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'])
        if rc: say(gid, 'commit failed', out[:200]); st[gid] = 'error'; return
        rc, out = run(['git', 'push', '-q', '-f', 'origin', gid], timeout=120)
        if rc: say(gid, 'push failed', out[:200]); st[gid] = 'error'; return
        time.sleep(max(0.0, self.last + GAP - time.time()))
        body = ('A %d-gate circuit (AND, OR, NOT, fan-in two) found by SAT-based exact synthesis; it is checked on all %d '
                'inputs with one left and one right vertex on.\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)'
                % (len(gates), k * k))
        st[gid] = 'sending'; save_state(st)
        rc, out = run(['gh', 'pr', 'create', '--repo', UP, '--head', '%s:%s' % (ME, gid), '--base', 'main',
                       '--title', gid, '--body', body], timeout=90)
        self.last = time.time()
        url = [l for l in out.splitlines() if l.startswith('https://')]
        if rc or not url:
            st[gid] = 'pr_failed'; say(gid, 'PR failed:', out[:300])
            if re.search(r'rate limit|too quickly|abuse', out, re.I): raise Stop('GitHub rate limit: ' + out[:200])
            return
        st[gid] = 'sent'; say(gid, 'SENT', url[0], '(%s; %d gates, size bound %d)' % (why, len(gates), s))
        with open(DIR + '/sent.txt', 'a', encoding='utf-8') as f: f.write('%s %s %s\n' % (datetime.now().isoformat(timespec='seconds'), gid, url[0]))

def solve_stream(items, budget):
    """items: [(gid, k, s, mask)] -> yields (gid, status, gates)"""
    name = 'batch_%d.txt' % int(time.time())
    with open(DIR + '/' + name, 'w', encoding='utf-8', newline='\n') as f:
        for gid, k, s, mask in items: f.write('%s %d %d %d\n' % (gid.split('-')[-1], k, s, mask))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'bash ~/ns/wave_solve2.sh %s/%s %d' % (WSL_DIR, name, budget)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, encoding='utf-8', errors='replace')
    byn = {gid.split('-')[-1]: gid for gid, *_ in items}
    for line in p.stdout:
        f = line.split()
        if len(f) < 3 or f[0] != 'RES' or f[1] not in byn: continue
        gates = []
        if len(f) > 3:
            for t in f[3].split(';'):
                if t: gates.append(tuple(int(x) for x in t.split(',')))
        yield byn[f[1]], f[2], gates
    p.wait()
    try: os.remove(DIR + '/' + name)
    except OSError: pass

def run_batch(items, budget, snap, st, sender, retry):
    say('batch of %d (budget %d s): %s' % (len(items), budget, ' '.join(i[0] for i in items)))
    threading.Thread(target=lambda: _safe(sender.fetch), daemon=True).start()
    for gid, status, gates in solve_stream(items, budget):
        k, s, mask, w, g = snap[gid]
        if status == 'SAT' and ok(k, mask, gates, s):
            say(gid, 'solved: %d gates (bound %d, weight %d)' % (len(gates), s, w))
            sender.send(gid, k, s, gates, g, st)
        elif status == 'UNSAT':
            st[gid] = 'unsat'; say(gid, 'UNSAT at bound', s)
        else:
            if budget == BUDGET1: retry.append(gid); st[gid] = 'retry'
            else: st[gid] = 'unknown'
            say(gid, status if status != 'SAT' else 'SAT but failed verification')
        save_state(st)

def _safe(f):
    try: f()
    except Stop as e: say('STOP (fetch):', e)

def selftest():
    """solve one merged 5x5 instance and build its file with lake, to check the template end to end"""
    stmt = ('∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ '
            'PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C')
    gid = 'L-meta-99999901'
    g = {'statement': stmt, 'imports': ['PEqualNP.Defs']}
    t0 = time.time()
    res = list(solve_stream([(gid, 5, 8, 7572604)], BUDGET1))
    say('selftest solve:', res[0][1], len(res[0][2]), 'gates in %.1f s' % (time.time() - t0), 'verified' if ok(5, 7572604, res[0][2], 8) else 'NOT verified')
    path = os.path.join(DIR, 'L_meta_99999901.lean')
    open(path, 'w', encoding='utf-8', newline='\n').write(lean_file(gid, 5, res[0][2], g))
    t0 = time.time()
    rc, out = run(['lake', 'env', 'lean', path], cwd=ROOT + '/lean', timeout=900)
    say('selftest lean: rc', rc, '%.0f s' % (time.time() - t0), out[:400])

def main():
    subprocess.run(['wsl.exe', '-e', 'bash', '-lc', "sed 's/\\r$//' %s/wave_solve2.sh > ~/ns/wave_solve2.sh" % WSL_DIR])
    if '--selftest' in sys.argv: selftest(); return
    st = load_state(); sender = Sender(); retry = []
    snap = snapshot()
    if not st:
        for gid in snap: st[gid] = 'old'
        save_state(st); say('first start: %d open steps recorded as old' % len(snap))
    retry += [gid for gid, v in st.items() if v == 'retry' and gid in snap]
    say('racer up: %d open Represents steps (k<=5), %d to retry' % (len(snap), len(retry)))
    while True:
        try:
            snap = snapshot()
        except Exception as e:
            say('snapshot failed:', str(e)[:120]); time.sleep(POLL); continue
        new = sorted((gid for gid in snap if gid not in st), key=lambda x: -snap[x][3])
        try:
            if new:
                run_batch([(gid, snap[gid][0], snap[gid][1], snap[gid][2]) for gid in new], BUDGET1, snap, st, sender, retry)
                continue
            retry = [gid for gid in retry if gid in snap and st.get(gid) == 'retry']
            if retry:
                batch, retry = retry[:8], retry[8:]
                run_batch([(gid, snap[gid][0], snap[gid][1], snap[gid][2]) for gid in batch], BUDGET2, snap, st, sender, retry)
                continue
        except Stop as e:
            save_state(st); say('STOP:', e); return
        time.sleep(POLL)

if __name__ == '__main__':
    main()
