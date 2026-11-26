"""Wave racer for small circuit FIND steps: send a checked circuit within a minute of a step appearing.

Kinds of step it takes (the statement must match exactly):
  rep   : ∃ C, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin k => (MASK : ℕ).testBit (k * u.val + v.val)) C,  k <= 5
  rsam  : RepSizeAtMost (fun (u : Fin n) (v : Fin m) => (MASK : ℕ).testBit (m * u.val + v.val)) s   (AND/OR only)
  pair  : ∃ C, (FanInTwo | Monotone2) C ∧ C.size ≤ s ∧ ∀ i j : Fin n, C.eval (List.ofFn fun k : Fin n =>
          decide (k = i ∨ k = j)) = (MASK : ℕ).testBit (n * min i.val j.val + max i.val j.val)
Threads:
  - poller (main): reads gaps.json every POLL s. Each set of steps it has not seen before starts its own solve batch
    at once, so a new wave never waits for an earlier one.
  - solve batches: SAT exact synthesis (wave_solve2.sh), 16 at a time, results streamed back. Two stages: every
    step gets 3 s, then the steps still open get BUDGET1 s, so an easy step never waits behind hard ones. Each SAT
    result is verified in Python on every input row the statement asks about and queued for sending at once.
  - retry lane: steps the fast pass left UNKNOWN (and steps open since before the first start) get one BUDGET2
    pass, 16 at a time at the lowest CPU priority, so a new wave's searches still get the CPU first.
  - senders (two threads, one spare worktree each; heaviest step first): right before sending, the step is looked up
    in the poller's latest snapshot, with no desk call (the desk's /desk/step answered 429 at about one request
    every 2 s):
      gone from the snapshot: skip (proved or closed);
      the snapshot shows a PR: skip (someone sent first);
      otherwise: lease it from the desk with have=proof (join.txt: a proof of a unit you did not take earns only
      the floor of 10 points; a leased one earns its lease price). No lease: skip, or come back once when the
      desk names a time within 30 minutes.
    Then one Lean file on a branch named after the step, cut from upstream main in the sender's worktree, pushed
    to the fork; one PR with "Lease: <id>" at least GAP s after the last PR from either sender and under
    PR_HOUR_CAP an hour; then the lease is released with reason submitted. Desk calls are DESK_GAP s apart, and a
    429 pauses them. Steps under MIN_WEIGHT are skipped. Every PR is logged in sent2.tsv (mode, lease price).
Each step is sent at most once (state.json), so we never re-send to a closed step. On the very first start every
open step is recorded as 'old' and skipped. The racer exits on a STOP notice on upstream main, on a 429 from the desk,
or on a GitHub rate-limit answer.
usage: python -I -X utf8 -u .pnp/race/wave_racer.py [--selftest]
"""
import itertools, json, os, queue, re, subprocess, sys, time, threading, urllib.request, urllib.parse, urllib.error
from datetime import datetime, timezone

ROOT = os.environ.get('PNP_ROOT', os.getcwd())  # the proofs checkout
WTS = [os.path.join(os.path.dirname(ROOT), w) for w in ('pnp-race', 'pnp-race2')]  # one spare worktree per sender
WT = WTS[0]
DIR = ROOT + '/.pnp/race'
WSL_DIR = os.environ['PNP_RACE_WSL_DIR']  # DIR as WSL sees it, e.g. /mnt/c/.../.pnp/race
UP = 'open-goat/pequalnp-proofs'
UP_URL = 'https://github.com/%s.git' % UP
ME = os.environ['PNP_GH']  # your GitHub login (the fork's owner)
SNAP = 'https://data.pequalnp.com/data/desk/gaps.json'
DESK = 'https://pequalnp.com/desk'
POLL, BUDGET1, BUDGET2, RACE_WINDOW, GAP = 15, 20, 150, 45, 3
FAST, PAR_FAST = (3, BUDGET1), 16   # fast pass: every step gets 3 s, then the rest get 20 s, 16 searches at a time
WAIT_STEP, WAIT_TRIES = 10, 6
MAX_INPUTS, MAX_SIZE = 16, 24
P_REP = re.compile(r'^∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ '
                   r'PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C$')
P_RSAM = re.compile(r'^PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\) => \((\d+) : ℕ\)\.testBit '
                    r'\((\d+) \* u\.val \+ v\.val\)\) (\d+)$')
P_PAIR = re.compile(r'^∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.(FanInTwo|Monotone2) C ∧ C\.size ≤ (\d+) ∧ '
                    r'∀ i j : Fin (\d+), C\.eval \(List\.ofFn fun k : Fin (\d+) => decide \(k = i ∨ k = j\)\) = \((\d+) : ℕ\)\.testBit '
                    r'\((\d+) \* min i\.val j\.val \+ max i\.val j\.val\)$')
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

def parse(g):
    """the step as a dict (kind, n inputs, size bound s, allow_not, rows [(input bitmask, wanted)], solver spec) or None"""
    st = (g.get('statement') or '').strip()
    gid = g['id']; num = gid.split('-')[-1]
    m = P_REP.match(st)
    if m and m.group(2) == m.group(4) and int(m.group(2)) <= 5:
        k, s, mask = int(m.group(2)), int(m.group(1)), int(m.group(3))
        rows = [((1 << u) | (1 << (k + v)), (mask >> (k * u + v)) & 1) for u in range(k) for v in range(k)]
        return dict(kind='rep', id=gid, n=2 * k, s=s, allow=1, rows=rows, spec='rel:%d:%x' % (k, mask), g=g,
                    what='%dx%d Represents' % (k, k))
    m = P_RSAM.match(st)
    if m and m.group(2) == m.group(4):
        nl, nr, mask, s = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(5))
        if nl + nr > MAX_INPUTS or s > MAX_SIZE: return None
        rows = [((1 << u) | (1 << (nl + v)), (mask >> (nr * u + v)) & 1) for u in range(nl) for v in range(nr)]
        return dict(kind='rsam', id=gid, n=nl + nr, s=s, allow=0, rows=rows, spec='rel:%d:%x' % (nl, mask), g=g,
                    what='%dx%d RepSizeAtMost' % (nl, nr))
    m = P_PAIR.match(st)
    if m and m.group(3) == m.group(4) == m.group(6):
        n, s, mask, allow = int(m.group(3)), int(m.group(2)), int(m.group(5)), int(m.group(1) == 'FanInTwo')
        if n > MAX_INPUTS or s > MAX_SIZE: return None
        rows = [((1 << i) | (1 << j), (mask >> (n * i + j)) & 1) for i in range(n) for j in range(i, n)]
        return dict(kind='pair', id=gid, n=n, s=s, allow=allow, rows=rows, spec='care:%s/care/%s.txt' % (WSL_DIR, num), g=g,
                    what='%d-vertex pair function, %s' % (n, 'with NOT' if allow else 'monotone'))
    return None

def snapshot():
    """{id: step} for the open steps the racer can take"""
    req = urllib.request.Request(SNAP, headers={'User-Agent': 'curl/8.0', 'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(req, timeout=40) as r:
        G = json.load(r)['gaps']
    out = {}
    for g in G:
        if g.get('dead'): continue
        st = parse(g)
        if st: st['w'] = int(g.get('weight') or 0); out[g['id']] = st
    return out

def ok(step, gates):
    """the circuit has at most s gates, reads only earlier wires, uses NOT only where allowed, and is right on every row"""
    n = step['n']; out = n + len(gates) - 1
    if not gates or len(gates) > step['s']: return False
    for j, (o, a, b) in enumerate(gates):
        if o not in (0, 1, 2) or (o == 2 and not step['allow']): return False
        if not (0 <= a < n + j) or (o != 2 and not (0 <= b < n + j)): return False
    for r, want in step['rows']:
        w = [bool((r >> i) & 1) for i in range(n)]
        for o, a, b in gates:
            w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
        if w[out] != bool(want): return False
    return True

def lean_file(step, gates):
    """the whole proof file: the step's imports, the witness in a helper namespace, the theorem with the step's statement"""
    gid, g, n = step['id'], step['g'], step['n']
    name = 'PEqualNP.Outside.' + gid.replace('-', '_')
    ns = name + '.Helpers'
    ops = {0: 'and', 1: 'or', 2: 'not'}
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
    imports = g.get('imports') or ['PEqualNP.Defs']
    if step['kind'] == 'rep':
        k = n // 2
        doc = f'inputs 0..{k-1} are the left vertex, {k}..{n-1} the right vertex'
    elif step['kind'] == 'rsam':
        nl = int(step['spec'].split(':')[1])
        doc = f'inputs 0..{nl-1} are the left vertex, {nl}..{n-1} the right vertex'
    else:
        doc = f'inputs 0..{n-1} are the vertices; the statement turns on the two vertices of a pair (one when i = j)'
    cls = 'FanInTwo' if step['allow'] else 'Monotone2'
    unfold = '  unfold PEqualNP.Represents.RepSizeAtMost\n' if step['kind'] == 'rsam' else ''
    return (''.join('import %s\n' % i for i in imports) + '\n'
            f'namespace {ns}\n\nopen PEqualNP.CircuitLowerBounds\n\n'
            f'/-- A {len(gates)}-gate circuit found by SAT-based exact synthesis: {doc};\n'
            f'gate `j` writes wire `{n} + j`, the output is the last gate. -/\n'
            f'def witness : Circuit :=\n  ⟨[{gl}], {n + len(gates) - 1}⟩\n\nend {ns}\n\n'
            f'theorem {name} : {g["statement"].strip()} := by\n'
            f'{unfold}'
            f'  refine ⟨{ns}.witness, ?_, by decide, by decide +kernel⟩\n'
            f'  simp [PEqualNP.MetaComplexity.{cls}, {ns}.witness]\n')

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

LATEST = {'snap': {}, 't': 0.0}               # the poller's latest snapshot, read by the senders
MODEL = 'claude-opus-5-5'
MIN_WEIGHT = 20                               # weight-1 steps get stood down unchecked
DESK_GAP = 7.0                                # join.txt: one desk request every few seconds at most. At 4 s (about
                                              # 627 calls an hour) the desk answered 429 with a one-hour pause.
DESK_LOCK = threading.Lock(); DESK_LAST = [0.0]; DESK_PAUSED_UNTIL = [0.0]
FRESH = 300                                   # a step first seen this many seconds ago still counts as fresh
BACKLOG = set()                               # steps queued before a restart: re-solved, but never fresh
PR_HOUR_CAP = 400                            # GitHub refused PR creation after 500 in an hour
PR_TIMES = []

def desk_call(method, path, params):
    """one desk request, paced DESK_GAP s after the previous one; a 429 pauses every desk call (not the racer)"""
    with DESK_LOCK:
        while True:
            wait = max(DESK_LAST[0] + DESK_GAP, DESK_PAUSED_UNTIL[0]) - time.time()
            if wait <= 0: break
            time.sleep(min(wait, 30))
        DESK_LAST[0] = time.time()
        url = DESK + path + '?' + urllib.parse.urlencode(params)
        req = urllib.request.Request(url, method=method, headers={'User-Agent': 'curl/8.0'})
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                return r.status, json.load(r)
        except urllib.error.HTTPError as e:
            try: body = json.load(e)
            except Exception: body = {}
            if e.code == 429:
                ra = int(body.get('retry_after_s') or e.headers.get('Retry-After') or 600)
                DESK_PAUSED_UNTIL[0] = time.time() + ra
                with open(DIR + '/desk_pause.txt', 'w') as f: f.write('%.0f' % DESK_PAUSED_UNTIL[0])   # survives a restart
                say('desk answered 429; all desk calls paused for %d s' % ra)
            return e.code, body
        except Exception as e:
            return 0, {'error': repr(e)[:200]}

def lease(gid):
    """-> (lease id, points, None) or (None, None, (why, retry_after_s))"""
    code, d = desk_call('GET', '/next', {'handle': ME, 'value': 1, 'gap': gid, 'have': 'proof', 'model': MODEL})
    g, l = d.get('gap') or {}, d.get('lease') or {}
    if code == 200 and g.get('id') == gid and l.get('id'):
        return l['id'], (l.get('terms') or {}).get('points'), None
    if code == 200 and l.get('id') and g.get('id') != gid:   # the desk handed another step: give it back at once
        desk_call('POST', '/release', {'lease': l['id'], 'reason': 'other'})
        return None, None, ('the desk offered %s instead' % g.get('id'), None)
    why = re.sub(r'[^ -~]', ' ', str(d.get('note') or d.get('error') or d.get('say') or 'HTTP %s' % code))[:160]
    return None, None, (why, d.get('retry_after_s'))

def gh_capacity_wait():
    """keep PR creation under PR_HOUR_CAP per rolling hour"""
    while True:
        now = time.time()
        PR_TIMES[:] = [t for t in PR_TIMES if now - t < 3600]
        if len(PR_TIMES) < PR_HOUR_CAP: return
        time.sleep(30)

def record(step, url, mode, points):
    new = not os.path.exists(DIR + '/sent2.tsv')
    with open(DIR + '/sent2.tsv', 'a', encoding='utf-8') as f:
        if new: f.write('time\tstep\tpr\tmode\tlease_points\tweight\tkind\n')
        f.write('%s\t%s\t%s\t%s\t%s\t%s\t%s\n' % (datetime.now().isoformat(timespec='seconds'), step['id'], url.rsplit('/', 1)[-1],
                                                 mode, points if points is not None else '', step['w'], step['kind']))
PR_LOCK = threading.Lock(); LAST_PR = [0.0]   # PRs from all senders at least GAP s apart
SENDQ = queue.PriorityQueue(); SENDN = itertools.count()   # (not before, -weight, order, item): heaviest first

class Sender:
    def __init__(self, wt):
        self.wt = wt; self.fetched = 0.0; self.lock = threading.Lock()
        self.q = SENDQ; self.n = SENDN

    def put(self, item, when=0.0):
        # fresh steps (first seen under FRESH s ago) go ahead of backlog: that is where the close races are; then heaviest
        fresh = 0 if time.time() - item[0].get('seen', 0) < FRESH else 1
        self.q.put((when, fresh, -item[0]['w'], next(self.n), item))

    def fetch(self):
        with self.lock:
            if time.time() - self.fetched < 60: return
            rc, out = run(['git', 'fetch', '-q', UP_URL, 'main'], cwd=self.wt, timeout=90)
            if rc: say('fetch failed:', out[:200]); return
            if run(['git', 'cat-file', '-e', 'FETCH_HEAD:STOP'], cwd=self.wt)[0] == 0: raise Stop('STOP notice on upstream main')
            self.fetched = time.time()

    def loop(self):
        while not STOP.is_set():
            try: when, fresh, negw, n, item = self.q.get(timeout=1)
            except queue.Empty: continue
            if when > time.time():
                self.q.put((when, fresh, negw, n, item)); time.sleep(0.5); continue
            step, gates, tries = item
            try:
                res = self.send(step, gates)
            except Stop as e:
                say('STOP:', e); STOP.set(); return
            except Exception as e:
                res = 'error'; say(step['id'], 'send error:', repr(e)[:200])
            if isinstance(res, tuple) and res[0] == 'wait':   # the desk said when to come back
                self.put((step, gates, tries + 1), time.time() + res[1]); mark(step['id'], 'lease_wait'); continue
            mark(step['id'], res)

    def send(self, step, gates):
        # No desk call here: its /desk/step answered 429 at about one request every 2 s (November 26). The check is
        # against the latest snapshot instead (refreshed every POLL s): gone from it means proved or closed; a PR
        # in it means someone sent first, at least a snapshot ago.
        gid, g = step['id'], step['g']
        now = LATEST['snap'].get(gid)
        if now is None:
            say(gid, 'not sent: no longer in the snapshot (proved or closed)'); return 'gone'
        pr = str(now['g'].get('pr_open'))
        if pr not in ('0', 'None'):
            say(gid, 'late: the snapshot shows %s PR(s)' % pr); return 'late'
        gh_capacity_wait()   # never hold a lease while GitHub would refuse the PR
        if now['g'].get('held_now') and not step.get('held_retried'):   # someone holds it: no desk call now
            step['held_retried'] = True
            say(gid, 'held by another agent per the snapshot; looking again in 10 minutes')
            return ('wait', 600)
        # The branch is built and pushed BEFORE the lease, so the PR opens seconds after the lease is granted:
        # races on fresh steps were being lost by 5-36 s. A pushed branch without a lease is just left unused.
        self.fetch()
        path = g.get('file') or 'lean/PEqualNP/Outside/%s.lean' % gid.replace('-', '_')
        if run(['git', 'cat-file', '-e', 'FETCH_HEAD:' + path], cwd=self.wt)[0] == 0:
            say(gid, 'already on main'); return 'on_main'
        rc, out = run(['git', 'checkout', '-q', '-f', '-B', gid, 'FETCH_HEAD'], cwd=self.wt)
        if rc: say(gid, 'checkout failed', out[:200]); return 'error'
        with open(self.wt + '/' + path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(lean_file(step, gates))
        run(['git', 'add', path], cwd=self.wt)
        rc, out = run(['git', 'commit', '-q', '-m', gid + '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'], cwd=self.wt)
        if rc: say(gid, 'commit failed', out[:200]); return 'error'
        rc, out = run(['git', 'push', '-q', '-f', 'origin', gid], cwd=self.wt, timeout=120)
        if rc: say(gid, 'push failed', out[:200]); return 'error'
        lid, points, refused = lease(gid)
        if lid: say(gid, 'leased (%s points), lease %s' % (points, lid))
        if not lid:
            why_not, retry = refused
            say(gid, 'no lease: %s%s' % (why_not, ' (retry in %s s)' % retry if retry else ''))
            if retry and int(retry) <= 1800 and not step.get('lease_retried'):
                step['lease_retried'] = True
                return ('wait', int(retry) + 5)
            return 'no_lease'
        why = 'leased at %s points' % points
        def give_back(reason, result):
            desk_call('POST', '/release', {'lease': lid, 'reason': reason})
            return result
        body =('Lease: %s\n\nA %d-gate circuit (%s, fan-in at most two) found by SAT-based exact synthesis; it is checked on all %d '
                'inputs the statement asks about.\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)'
                % (lid, len(gates), 'AND, OR, NOT' if step['allow'] else 'AND and OR', len(step['rows'])))
        mark(gid, 'sending')
        for attempt in (1, 2):
            gh_capacity_wait()
            with PR_LOCK:
                time.sleep(max(0.0, LAST_PR[0] + GAP - time.time()))
                LAST_PR[0] = time.time()
            rc, out = run(['gh', 'pr', 'create', '--repo', UP, '--head', '%s:%s' % (ME, gid), '--base', 'main',
                           '--title', gid, '--body', body], cwd=ROOT, timeout=90)
            PR_TIMES.append(time.time())
            url = [l for l in out.splitlines() if l.startswith('https://')]
            if not rc and url: break
            say(gid, 'PR failed:', out[:300])
            if attempt == 1 and re.search(r'rate limit|too quickly|abuse', out, re.I):
                say('GitHub rate limit: PRs paused for 15 minutes'); LAST_PR[0] = time.time() + 900
                time.sleep(900)
                code, d = desk_call('POST', '/beat', {'lease': lid})   # renew the lease; 410 withdrawn: do not send
                if code == 410 and (d or {}).get('withdrawn'):
                    say(gid, 'lease withdrawn while paused; not sent'); return 'withdrawn'
                continue
            return give_back('other', 'pr_failed')
        desk_call('POST', '/release', {'lease': lid, 'reason': 'submitted'})
        say(gid, 'SENT', url[0], '(%s; %s, %d gates, size bound %d)' % (why, step['what'], len(gates), step['s']))
        with open(DIR + '/sent.txt', 'a', encoding='utf-8') as f:
            f.write('%s %s %s\n' % (datetime.now().isoformat(timespec='seconds'), gid, url[0]))
        record(step, url[0], 'lease', points)
        return 'sent'

def solve_stream(steps, budget, par=8, nice=0):
    """steps: [step] -> yields (gid, status, gates) as each search ends"""
    os.makedirs(DIR + '/care', exist_ok=True)
    name = 'batch_%d_%d.txt' % (int(time.time() * 1000), threading.get_ident() % 10000)
    with open(DIR + '/' + name, 'w', encoding='utf-8', newline='\n') as f:
        for st in steps:
            num = st['id'].split('-')[-1]
            if st['spec'].startswith('care:'):
                with open(DIR + '/care/%s.txt' % num, 'w', encoding='utf-8', newline='\n') as c:
                    c.write(''.join('%d %d\n' % r for r in st['rows']))
            f.write('%s %d %s %d %d\n' % (num, st['n'], st['spec'], st['s'], st['allow']))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'bash ~/ns/wave_solve2.sh %s/%s %d %d %d' % (WSL_DIR, name, budget, par, nice)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, encoding='utf-8', errors='replace')
    byn = {st['id'].split('-')[-1]: st['id'] for st in steps}
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

def batch(steps, budgets, sender, par=PAR_FAST, nice=0, retry_lane=False):
    """one stage per budget, each stage on the steps the last left UNKNOWN (short budgets first, so an easy step
    never waits behind a hard one)"""
    info = {st['id']: st for st in steps}
    say('%s of %d (budgets %s s, %d at a time): %s' % ('retry batch' if retry_lane else 'batch', len(steps),
        '/'.join(map(str, budgets)), par, ' '.join(info)))
    threading.Thread(target=lambda: _safe(sender.fetch), daemon=True).start()
    todo = list(steps)
    try:
        for i, budget in enumerate(budgets):
            last = i == len(budgets) - 1; left = []
            for gid, status, gates in solve_stream(todo, budget, par, nice):
                st = info[gid]
                if status == 'SAT' and ok(st, gates):
                    say(gid, 'solved: %s, %d gates (bound %d, weight %d, %d s stage)' % (st['what'], len(gates), st['s'], st['w'], budget))
                    mark(gid, 'queued'); sender.put((st, gates, 0))
                elif status == 'UNSAT':
                    mark(gid, 'unsat'); say(gid, 'UNSAT at bound', st['s'], '(%s)' % st['what'])
                elif not last:
                    left.append(st)
                elif not retry_lane:
                    mark(gid, 'retry')
                    with RETRY_LOCK: RETRY.append(st)
                    say(gid, status if status != 'SAT' else 'SAT but failed verification', '-> retry lane')
                else:
                    mark(gid, 'unknown'); say(gid, status, 'after the long pass')
            if not last and left:
                say('%d left after the %d s stage' % (len(left), budget))
            todo = left
            if not todo: break
    except Exception as e:
        say('batch error:', repr(e)[:200])

def _safe(f):
    try: f()
    except Stop as e: say('STOP (fetch):', e); STOP.set()

def selftest():
    """for each kind, solve open steps of that kind until one is SAT, write its file and build it with lake (no send)"""
    snap = snapshot()
    for kind in ('rep', 'rsam', 'pair'):
        cands = [st for st in snap.values() if st['kind'] == kind and (kind != 'pair' or True)]
        if kind == 'pair':  # one with NOT and one monotone
            cands = [st for st in cands if st['allow']][:6] + [st for st in cands if not st['allow']][:6]
        else:
            cands = cands[:6]
        if not cands: say('selftest', kind, ': no open step of this kind'); continue
        done = set()
        for gid, status, gates in solve_stream(cands, 10, 12):
            st = next(c for c in cands if c['id'] == gid)
            key = (kind, st['allow'])
            if status != 'SAT' or key in done: continue
            done.add(key)
            v = ok(st, gates)
            path = DIR + '/selftest_%s.lean' % gid.replace('-', '_')
            open(path, 'w', encoding='utf-8', newline='\n').write(lean_file(st, gates))
            t0 = time.time()
            rc, out = run(['lake', 'env', 'lean', path], cwd=ROOT + '/lean', timeout=900)
            say('selftest %s (%s) %s: %d gates, python %s, lean rc %d in %.0f s %s' % (kind, st['what'], gid, len(gates),
                'ok' if v else 'FAILED', rc, time.time() - t0, out[:300]))
            os.remove(path)
        if not done: say('selftest', kind, ': none of %d solved in 10 s' % len(cands))

def main():
    subprocess.run(['wsl.exe', '-e', 'bash', '-lc', "sed 's/\\r$//' %s/wave_solve2.sh > ~/ns/wave_solve2.sh" % WSL_DIR])
    if '--selftest' in sys.argv: selftest(); return
    ST.update(load_state())
    try:   # a desk pause from before a restart still holds
        DESK_PAUSED_UNTIL[0] = float(open(DIR + '/desk_pause.txt').read().strip())
        if DESK_PAUSED_UNTIL[0] > time.time(): say('desk calls paused for another %.0f s (earlier 429)' % (DESK_PAUSED_UNTIL[0] - time.time()))
    except (FileNotFoundError, ValueError): pass
    try:   # PRs already sent in the last hour count toward the GitHub cap
        for line in open(DIR + '/sent.txt', encoding='utf-8'):
            t = datetime.fromisoformat(line.split()[0]).timestamp()
            if time.time() - t < 3600: PR_TIMES.append(t)
    except FileNotFoundError: pass
    say('PRs sent in the last hour: %d (cap %d)' % (len(PR_TIMES), PR_HOUR_CAP))
    senders = [Sender(wt) for wt in WTS]
    for s_ in senders: threading.Thread(target=s_.loop, daemon=True).start()
    sender = senders[0]
    snap = snapshot()
    LATEST['snap'], LATEST['t'] = snap, time.time()
    if not ST:
        for gid in snap: mark(gid, 'old')
        say('first start: %d open steps recorded as old' % len(snap))
    for gid, v in list(ST.items()):  # interrupted fast searches start again as new; 'sending' is never repeated
        if v in ('solving', 'queued', 'lease_wait'):
            with ST_LOCK: del ST[gid]
            BACKLOG.add(gid)   # solved again after the restart, but not fresh
        elif v == 'retry' and gid in snap:
            RETRY.append(snap[gid])
        elif v == 'old' and gid in snap and snap[gid]['w'] >= MIN_WEIGHT and str(snap[gid]['g'].get('pr_open')) in ('0', 'None'):
            RETRY.append(snap[gid]); mark(gid, 'retry')   # open since before the first start, never tried
    kinds = {}
    for st in snap.values(): kinds[st['kind']] = kinds.get(st['kind'], 0) + 1
    say('racer up: %d open steps it can take %s, %d to retry' % (len(snap), kinds, len(RETRY)))
    retry_thread = None
    while not STOP.is_set():
        try:
            snap = snapshot()
            LATEST['snap'], LATEST['t'] = snap, time.time()
        except Exception as e:
            say('snapshot failed:', str(e)[:120]); STOP.wait(POLL); continue
        # A step the snapshot already shows with a PR is skipped (that PR is older than the race window by now), but
        # it is looked at again if its PRs close and it shows up open with no PR.
        new = []
        for gid, st in snap.items():
            if gid in ST and ST[gid] != 'had_pr': continue
            if st['w'] < MIN_WEIGHT:
                mark(gid, 'light'); continue
            if str(st['g'].get('pr_open')) not in ('0', 'None'):
                if gid not in ST: mark(gid, 'had_pr')
                continue
            new.append(gid)
        new.sort(key=lambda x: (-snap[x]['w'], -int(x.split('-')[-1])))   # heaviest first, then newest
        if new:
            for gid in new: mark(gid, 'solving'); snap[gid]['seen'] = 0 if gid in BACKLOG else time.time()
            threading.Thread(target=batch, args=([snap[gid] for gid in new], FAST, sender), daemon=True).start()
        if retry_thread is None or not retry_thread.is_alive():
            with RETRY_LOCK:
                RETRY[:] = [st for st in RETRY if st['id'] in snap and ST.get(st['id']) == 'retry']
                todo, RETRY[:] = RETRY[:16], RETRY[16:]
            if todo:   # all 16 threads at the lowest priority: a new wave's searches still get the CPU first
                retry_thread = threading.Thread(target=batch, args=(todo, (BUDGET2,), sender, 16, 1, True), daemon=True)
                retry_thread.start()
        STOP.wait(POLL)
    say('racer stopped')

if __name__ == '__main__':
    main()
