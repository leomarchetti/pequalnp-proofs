"""Exact representation costs of all n x n bipartite graphs (one class per symmetry orbit), on the one-a-side promise:
  m = least AND/OR fan-in-two circuit (RepSizeAtMost),  g = least AND/OR/NOT fan-in-two circuit (Represents + FanInTwo).
Each (class, mode) keeps a proven interval [lb, ub]: every size below lb is UNSAT, a circuit of size ub exists.
  - ub starts from a construction (rows grouped by their column sets, or columns by their row sets), so no solver time
    goes into finding upper bounds; g <= m is used both ways.
  - Pass 1 (every class): ask the solver at size lb with a short budget; SAT closes the job, UNSAT raises lb, a timeout
    parks the job.
  - Later passes, longer budgets: only jobs whose interval still allows a break of one of the conjectures (see check.py),
    asked at lb (to raise it) and at ub - 1 (to lower it).
State: table_<n>.json, rewritten after every batch. Log: explore_<n>.log.
usage: python explore.py n [budget1 budget2 budget3]   (seconds per solver call; default 20 120 600)"""
import json, os, subprocess, sys, time
n = int(sys.argv[1]); B = [int(x) for x in sys.argv[2:5]] or [20, 120, 600]
DIR = os.path.dirname(os.path.abspath(__file__))
WSL_DIR = '/mnt/c/<path-to-checkout>/.pnp/explore'
C = json.load(open(os.path.join(DIR, 'classes_%d.json' % n)))
TP = os.path.join(DIR, 'table_%d.json' % n)
full = (1 << (n * n)) - 1
BOUND = {'comp': 2 * n - 4, 'not': 2 * n - 5}   # the sharper conjectures (19385, 19158); 19037's 2n is weaker than 19385's

def log(*a):
    line = time.strftime('%H:%M:%S ') + ' '.join(map(str, a))
    print(line, flush=True)
    open(os.path.join(DIR, 'explore_%d.log' % n), 'a').write(line + '\n')

def nbrs(mask, side):
    if side == 'row': return [(mask >> (n * u)) & ((1 << n) - 1) for u in range(n)]
    return [sum(((mask >> (n * u + v)) & 1) << u for u in range(n)) for v in range(n)]

def construction(mask):
    """gates of the better of: group rows by their column sets (OR of the group's rows AND OR of the set's columns,
    then OR over the groups), or the same with columns; a full set needs no AND; one gate for the complete graph"""
    if mask == 0: return 0
    if mask == full: return 1
    best = None
    for side in ('row', 'col'):
        groups = {}
        for i, s in enumerate(nbrs(mask, side)):
            if s: groups.setdefault(s, []).append(i)
        cost = len(groups) - 1                         # ORs joining the terms
        for s, members in groups.items():
            k = bin(s).count('1')
            cost += (len(members) - 1) + (0 if k == n else (k - 1) + 1)
        best = cost if best is None else min(best, cost)
    return best

def trivial(mask):
    if mask == 0: return 0
    if mask == full: return 1
    if any(s == (1 << n) - 1 for s in nbrs(mask, 'row')) and bin(mask).count('1') == n: return 0   # one full row
    if any(s == (1 << n) - 1 for s in nbrs(mask, 'col')) and bin(mask).count('1') == n: return 0   # one full column
    return None

T = json.load(open(TP)) if os.path.exists(TP) else {}
for i, c in enumerate(C):
    k = str(i)
    r = T.setdefault(k, {'mask': c['mask'], 'comp': c['comp'], 'g': [1, None], 'm': [1, None]})
    t = trivial(c['mask'])
    if t is not None: r['g'] = [t, t]; r['m'] = [t, t]; continue
    ub = construction(c['mask'])
    for mode in ('g', 'm'):
        if r[mode][1] is None or r[mode][1] > ub: r[mode][1] = ub
    r.pop('hard', None); r.pop('probe_g', None); r.pop('probe_m', None)

def save():
    tmp = TP + '.tmp'; json.dump(T, open(tmp, 'w')); os.replace(tmp, TP)

def tighten():
    for r in T.values():
        g, m = r['g'], r['m']
        if m[0] < g[0]: m[0] = g[0]
        if g[1] > m[1]: g[1] = m[1]

def is_open(x): return x[0] < x[1]

def relevant():
    """(key, mode) pairs whose interval still allows a break of 19385 or 19158"""
    out = set()
    for k, r in T.items():
        c = T[str(r['comp'])]
        if r['m'][1] - c['m'][0] > BOUND['comp']:            # m(A) - m(comp) could exceed 2n - 4
            if is_open(r['m']): out.add((k, 'm'))
            if is_open(c['m']): out.add((str(r['comp']), 'm'))
        if r['m'][1] - r['g'][0] > BOUND['not']:              # m(A) - g(A) could exceed 2n - 5
            if is_open(r['m']): out.add((k, 'm'))
            if is_open(r['g']): out.add((k, 'g'))
    return out

def run(jobs, budget):
    """jobs: [(key, mode, size)] -> {(key, mode, size): status}"""
    name = 'batch_%d.txt' % int(time.time() * 1000)
    with open(os.path.join(DIR, name), 'w', newline='\n') as f:
        for j, (k, mode, s) in enumerate(jobs):
            f.write('%d %d rel:%d:%x %d %d\n' % (j, 2 * n, n, T[k]['mask'], s, 1 if mode == 'g' else 0))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'nice -n 10 bash ~/ns/explore_solve.sh %s/%s %d 16' % (WSL_DIR, name, budget)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    out = {}
    for line in p.stdout:
        f = line.split()
        if len(f) >= 3 and f[0] == 'RES' and f[1].isdigit() and int(f[1]) < len(jobs):
            gates = [[int(x) for x in t.split(',')] for t in (f[3].split(';') if len(f) > 3 else []) if t]
            out[jobs[int(f[1])]] = (f[2], gates)
    p.wait(); os.remove(os.path.join(DIR, name))
    return out

def apply(res):
    stats = {'SAT': 0, 'UNSAT': 0, 'other': 0}
    for (k, mode, s), (st, gates) in res.items():
        x = T[k][mode]
        if st == 'SAT':
            if s <= x[1] and gates: T[k]['circ_' + mode] = gates   # keep the circuit: the bank reuses it
            x[1] = min(x[1], s); stats['SAT'] += 1
        elif st == 'UNSAT': x[0] = max(x[0], s + 1); stats['UNSAT'] += 1
        else: stats['other'] += 1
    tighten(); save()
    return stats

def exact_count(): return sum(1 for r in T.values() for mode in ('g', 'm') if not is_open(r[mode]))

tighten(); save()
log('start: %d classes, %d of %d values exact from constructions and trivial cases' % (len(T), exact_count(), 2 * len(T)))
parked = set()
# pass 1: every open job, short budget, raise lb until SAT, UNSAT-at-ub or a timeout
rnd = 0
while True:
    jobs = [(k, mode, r[mode][0]) for k, r in T.items() for mode in ('g', 'm') if is_open(r[mode]) and (k, mode) not in parked]
    if not jobs: break
    rnd += 1; t0 = time.time(); res = run(jobs, B[0])
    for (k, mode, s), (st, _) in res.items():
        if st not in ('SAT', 'UNSAT'): parked.add((k, mode))
    for j in jobs:
        if j not in res: parked.add(j[:2])
    st = apply(res)
    log('pass 1 round %d: %d jobs in %.0f s -> %s | exact %d of %d | parked %d' % (rnd, len(jobs), time.time() - t0, st, exact_count(), 2 * len(T), len(parked)))
# later passes: only jobs that matter for the conjectures, ask at lb and at ub - 1
for level, budget in enumerate(B[1:], 2):
    tried = set()
    while True:
        rel = sorted(relevant())
        jobs = []
        for k, mode in rel:
            lb, ub = T[k][mode]
            for s in sorted({lb, ub - 1}):
                if (k, mode, s, budget) not in tried: jobs.append((k, mode, s)); tried.add((k, mode, s, budget))
        if not jobs: break
        t0 = time.time(); res = run(jobs, budget); st = apply(res)
        log('pass %d (budget %d s): %d jobs for %d relevant values in %.0f s -> %s | exact %d | still relevant %d'
            % (level, budget, len(jobs), len(rel), time.time() - t0, st, exact_count(), len(relevant())))
        if st['SAT'] + st['UNSAT'] == 0: break
log('done; relevant values left open:', len(relevant()))
