"""Wave racer for plain Represents FIND steps (k <= 5): send a checked circuit within a minute of a step appearing.

Threads:
  - poller (main): reads gaps.json every POLL s. Each set of steps it has not seen before starts its own solve batch
    at once, so a new wave never waits for an earlier one.
  - solve batches: one WSL call each (wave_solve2.sh): AND/OR/NOT SAT, BUDGET1 s per step, 8 at a time, results
    streamed back. Each SAT result is verified in Python and queued for sending as soon as it arrives.
  - retry lane: steps the fast pass left UNKNOWN get one BUDGET2 pass, 4 at a time at the lowest CPU priority, one
    retry batch at a time.
  - sender (one thread, so git work and PRs are serial): asks the desk about the step right before sending:
      open, leased or no answer: send;
      pr_open: send only while every competing PR is younger than RACE_WINDOW s;
      not_open (a step that has just appeared): look again every 10 s, up to 6 times;
      anything else: skip.
    Send means one Lean file on a branch named after the step, cut from upstream main in the ../pnp-race worktree,
    pushed to the fork, then one PR at least GAP s after the last.
Each step is sent at most once (state.json), so we never re-send to a closed step. Steps already open when the racer
first starts are recorded as 'old' and skipped. The racer exits on a STOP notice on upstream main, on a 429 from
the desk, or on a GitHub rate-limit answer.
usage: python -I -X utf8 -u .pnp/race/wave_racer.py [--selftest]
"""
import itertools, json, os, queue, re, subprocess, sys, time, threading, urllib.request, urllib.parse, urllib.error
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
POLL, BUDGET1, BUDGET2, RACE_WINDOW, GAP = 15, 20, 150, 45, 3
WAIT_STEP, WAIT_TRIES = 10, 6
PAT = re.compile(r'^∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ '
                 r'PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C$')
STOP = threading.Event()
LOG_LOCK, ST_LOCK = threading.Lock(), threading.Lock()

def say(*a):
    line = datetime.now().strftime('%H:%M:%S ') + ' '.join(str(x) for x in a)
    with LOG_LOCK:
        print(line, flush=True)
        with open(DIR + '/race.log', 'a', encoding='utf-8') as f: f.write(line + '\n')

def load_state():
    try: return json.load(open(DIR + '/state.json', encoding='utf-8'))
    except FileNotFoundError: return {}

ST = {}
def mark(gid, v):
    with ST_LOCK:
        ST[gid] = v
        tmp = DIR + '/state.json.tmp'
        json.dump(ST, open(tmp, 'w', encoding='utf-8'), indent=0, sort_keys=True)
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
    for j, (o, a, b) in enumerate(gates):
        if o not in (0, 1, 2) or not (0 <= a < n + j) or (o != 2 and not (0 <= b < n + j)): return False
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
        self.q = queue.PriorityQueue(); self.n = itertools.count()

    def put(self, item, when=0.0):
        self.q.put((when, next(self.n), item))

    def fetch(self):
        with self.lock:
            if time.time() - self.fetched < 60: return
            rc, out = run(['git', 'fetch', '-q', UP_URL, 'main'], timeout=90)
            if rc: say('fetch failed:', out[:200]); return
            if run(['git', 'cat-file', '-e', 'FETCH_HEAD:STOP'])[0] == 0: raise Stop('STOP notice on upstream main')
            self.fetched = time.time()

    def loop(self):
        while not STOP.is_set():
            try: when, n, item = self.q.get(timeout=1)
            except queue.Empty: continue
            if when > time.time():
                self.q.put((when, n, item)); time.sleep(0.5); continue
            gid, k, s, gates, g, tries = item
            try:
                res = self.send(gid, k, s, gates, g)
            except Stop as e:
                say('STOP:', e); STOP.set(); return
            except Exception as e:
                res = 'error'; say(gid, 'send error:', repr(e)[:200])
            if res == 'wait':
                if tries + 1 < WAIT_TRIES:
                    self.put((gid, k, s, gates, g, tries + 1), time.time() + WAIT_STEP); continue
                res = 'not_open'; say(gid, 'still not open after %d checks; not sent' % WAIT_TRIES)
            mark(gid, res)

    def send(self, gid, k, s, gates, g):
        d = desk_state(gid)
        state = d.get('state')
        if state in ('open', 'leased') or state is None:
            why = 'desk: %s' % (state or 'no answer')
        elif state == 'pr_open':
            ages = [pr_age(p) for p in (d.get('prs') or [])]
            if ages and max(ages) > RACE_WINDOW:
                say(gid, 'late: competing PR(s) %s, oldest %.0f s' % (d.get('prs'), max(ages))); return 'late'
            why = 'racing PR(s) %s, oldest %.0f s' % (d.get('prs'), max(ages) if ages else 0)
        elif state == 'not_open':
            say(gid, 'desk says not_open; looking again in %d s' % WAIT_STEP); return 'wait'
        else:
            say(gid, 'not sent, desk state', state); return 'closed:' + str(state)
        self.fetch()
        path = g.get('file') or 'lean/PEqualNP/Outside/%s.lean' % gid.replace('-', '_')
        if run(['git', 'cat-file', '-e', 'FETCH_HEAD:' + path])[0] == 0:
            say(gid, 'already on main'); return 'on_main'
        rc, out = run(['git', 'checkout', '-q', '-f', '-B', gid, 'FETCH_HEAD'])
        if rc: say(gid, 'checkout failed', out[:200]); return 'error'
        with open(WT + '/' + path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(lean_file(gid, k, gates, g))
        run(['git', 'add', path])
        rc, out = run(['git', 'commit', '-q', '-m', gid + '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'])
        if rc: say(gid, 'commit failed', out[:200]); return 'error'
        rc, out = run(['git', 'push', '-q', '-f', 'origin', gid], timeout=120)
        if rc: say(gid, 'push failed', out[:200]); return 'error'
        time.sleep(max(0.0, self.last + GAP - time.time()))
        body = ('A %d-gate circuit (AND, OR, NOT, fan-in two) found by SAT-based exact synthesis; it is checked on all %d '
                'inputs with one left and one right vertex on.\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)'
                % (len(gates), k * k))
        mark(gid, 'sending')
        rc, out = run(['gh', 'pr', 'create', '--repo', UP, '--head', '%s:%s' % (ME, gid), '--base', 'main',
                       '--title', gid, '--body', body], timeout=90)
        self.last = time.time()
        url = [l for l in out.splitlines() if l.startswith('https://')]
        if rc or not url:
            say(gid, 'PR failed:', out[:300])
            if re.search(r'rate limit|too quickly|abuse', out, re.I): raise Stop('GitHub rate limit: ' + out[:200])
            return 'pr_failed'
        say(gid, 'SENT', url[0], '(%s; %d gates, size bound %d)' % (why, len(gates), s))
        with open(DIR + '/sent.txt', 'a', encoding='utf-8') as f:
            f.write('%s %s %s\n' % (datetime.now().isoformat(timespec='seconds'), gid, url[0]))
        return 'sent'

def solve_stream(items, budget, par=8, nice=0):
    """items: [(gid, k, s, mask, ...)] -> yields (gid, status, gates) as each search ends"""
    name = 'batch_%d_%d.txt' % (int(time.time() * 1000), threading.get_ident() % 10000)
    with open(DIR + '/' + name, 'w', encoding='utf-8', newline='\n') as f:
        for it in items: f.write('%s %d %d %d\n' % (it[0].split('-')[-1], it[1], it[2], it[3]))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'bash ~/ns/wave_solve2.sh %s/%s %d %d %d' % (WSL_DIR, name, budget, par, nice)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, encoding='utf-8', errors='replace')
    byn = {it[0].split('-')[-1]: it[0] for it in items}
    try:
        for line in p.stdout:
            f = line.split()
            if len(f) < 3 or f[0] != 'RES' or f[1] not in byn: continue
            gates = [tuple(int(x) for x in t.split(',')) for t in (f[3].split(';') if len(f) > 3 else []) if t]
            yield byn[f[1]], f[2], gates
    finally:
        p.wait()
        try: os.remove(DIR + '/' + name)
        except OSError: pass

RETRY = []; RETRY_LOCK = threading.Lock()

def batch(items, budget, sender, par=8, nice=0):
    """items: [(gid, k, s, mask, weight, gap)]"""
    info = {it[0]: it for it in items}
    say('%s of %d (budget %d s): %s' % ('batch' if budget == BUDGET1 else 'retry batch', len(items), budget, ' '.join(info)))
    threading.Thread(target=lambda: _safe(sender.fetch), daemon=True).start()
    try:
        for gid, status, gates in solve_stream(items, budget, par, nice):
            _, k, s, mask, w, g = info[gid]
            if status == 'SAT' and ok(k, mask, gates, s):
                say(gid, 'solved: %d gates (bound %d, weight %d)' % (len(gates), s, w))
                mark(gid, 'queued'); sender.put((gid, k, s, gates, g, 0))
            elif status == 'UNSAT':
                mark(gid, 'unsat'); say(gid, 'UNSAT at bound', s)
            elif budget == BUDGET1:
                mark(gid, 'retry')
                with RETRY_LOCK: RETRY.append(info[gid])
                say(gid, status if status != 'SAT' else 'SAT but failed verification', '-> retry lane')
            else:
                mark(gid, 'unknown'); say(gid, status, 'after the long pass')
    except Exception as e:
        say('batch error:', repr(e)[:200])

def _safe(f):
    try: f()
    except Stop as e: say('STOP (fetch):', e); STOP.set()

def selftest():
    """solve one merged 5x5 instance and build its file with lake, to check the template end to end"""
    stmt = ('∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ '
            'PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C')
    gid = 'L-meta-99999901'
    g = {'statement': stmt, 'imports': ['PEqualNP.Defs']}
    t0 = time.time()
    res = list(solve_stream([(gid, 5, 8, 7572604)], BUDGET1))
    say('selftest solve:', res[0][1], len(res[0][2]), 'gates in %.1f s' % (time.time() - t0), 'verified' if ok(5, 7572604, res[0][2], 8) else 'NOT verified')
    path = DIR + '/L_meta_99999901.lean'
    open(path, 'w', encoding='utf-8', newline='\n').write(lean_file(gid, 5, res[0][2], g))
    t0 = time.time()
    rc, out = run(['lake', 'env', 'lean', path], cwd=ROOT + '/lean', timeout=900)
    say('selftest lean: rc', rc, '%.0f s' % (time.time() - t0), out[:400])
    os.remove(path)

def main():
    subprocess.run(['wsl.exe', '-e', 'bash', '-lc', "sed 's/\\r$//' %s/wave_solve2.sh > ~/ns/wave_solve2.sh" % WSL_DIR])
    if '--selftest' in sys.argv: selftest(); return
    ST.update(load_state())
    sender = Sender()
    threading.Thread(target=sender.loop, daemon=True).start()
    snap = snapshot()
    if not ST:
        for gid in snap: mark(gid, 'old')
        say('first start: %d open steps recorded as old' % len(snap))
    for gid, v in list(ST.items()):  # interrupted searches go to the retry lane; 'sending' is never repeated
        if v in ('retry', 'solving', 'queued') and gid in snap:
            RETRY.append((gid,) + snap[gid]); mark(gid, 'retry')
    say('racer up: %d open Represents steps (k<=5), %d to retry' % (len(snap), len(RETRY)))
    retry_thread = None
    while not STOP.is_set():
        try:
            snap = snapshot()
        except Exception as e:
            say('snapshot failed:', str(e)[:120]); STOP.wait(POLL); continue
        new = sorted((gid for gid in snap if gid not in ST), key=lambda x: -snap[x][3])
        if new:
            for gid in new: mark(gid, 'solving')
            threading.Thread(target=batch, args=([(gid,) + snap[gid] for gid in new], BUDGET1, sender), daemon=True).start()
        if retry_thread is None or not retry_thread.is_alive():
            with RETRY_LOCK:
                RETRY[:] = [it for it in RETRY if it[0] in snap and ST.get(it[0]) == 'retry']
                todo, RETRY[:] = RETRY[:4], RETRY[4:]
            if todo:
                retry_thread = threading.Thread(target=batch, args=(todo, BUDGET2, sender, 4, 1), daemon=True)
                retry_thread.start()
        STOP.wait(POLL)
    say('racer stopped')

if __name__ == '__main__':
    main()
