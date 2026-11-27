"""Answer-bank builder for rep (n x m grids) and pair (n-vertex) classes: exact [lb, ub] per mode with a circuit of
size ub, written straight to bank_<kind>_<n>x<m>.json (and a resumable table_<kind>_<n>x<m>.json).
Modes: 'g' AND/OR/NOT, 'm' AND/OR. Uses g <= m both ways; ub from a construction where there is one.
Rounds: every open job is asked at lb with the short budget (SAT closes it and stores the circuit, UNSAT raises lb,
a timeout parks it); then parked jobs are asked again with the long budget, at lb and (when no ub is known) above it.
Pair graphs whose single-vertex bits force a non-monotone function have no AND/OR circuit: stored as [99, 99].
usage: python explore2.py rep n m [b1 b2] | python explore2.py pair n [b1 b2]"""
import json, os, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bank
kind = sys.argv[1]
if kind == 'rep': n, m = int(sys.argv[2]), int(sys.argv[3]); rest = sys.argv[4:]
else: n = m = int(sys.argv[2]); rest = sys.argv[3:]
B1, B2 = (int(rest[0]), int(rest[1])) if len(rest) >= 2 else (20, 120)
PAR = int(os.environ.get('PAR', '6'))
DIR = bank.DIR; WSL_DIR = '/mnt/c/<path-to-checkout>/.pnp/explore'
tag = '%s_%dx%d' % (kind, n, m)
CL = json.load(open(os.path.join(DIR, 'classes_%s.json' % tag)))
TP = os.path.join(DIR, 'table_%s.json' % tag)
NI = n + m if kind == 'rep' else n
INF = 99

def log(*a):
    line = time.strftime('%H:%M:%S ') + ' '.join(map(str, a)); print(line, flush=True)
    open(os.path.join(DIR, 'explore_%s.log' % tag), 'a').write(line + '\n')

def rows_of(mask):   # (input bitmask over NI wires, wanted value) for every input the statement asks about
    if kind == 'rep': return [((1 << u) | (1 << (n + v)), (mask >> (m * u + v)) & 1) for u in range(n) for v in range(m)]
    return [((1 << i) | (1 << j), (mask >> (n * i + j)) & 1) for i in range(n) for j in range(i, n)]

def ok(gates, mask, allow):
    return (bank.rep_ok if kind == 'rep' else lambda g, mk, nn, mm, a: bank.pair_ok(g, mk, nn, a))(gates, mask, n, m, allow)

def pair_monotone_possible(mask):
    for i in range(n):
        if (mask >> (n * i + i)) & 1:
            for j in range(n):
                a, b = sorted((i, j))
                if not (mask >> (n * a + b)) & 1: return False
    return True

def pair_construction(mask):
    """AND/OR circuit when one exists: looped vertices are their own wire; the other edges are grouped as stars
    x_i AND (OR of the unlooped neighbours j > i); all terms ORed. None when no gate is needed or none exists"""
    if not pair_monotone_possible(mask): return None
    gates = []
    def OR(ws):
        cur = ws[0]
        for x in ws[1:]: gates.append([1, cur, x]); cur = n + len(gates) - 1
        return cur
    loop = [i for i in range(n) if (mask >> (n * i + i)) & 1]
    terms = list(loop)
    for i in range(n):
        if i in loop: continue
        nb = [j for j in range(i + 1, n) if j not in loop and (mask >> (n * i + j)) & 1]
        if nb:
            o = OR(nb); gates.append([0, i, o]); terms.append(n + len(gates) - 1)
    if not terms: return None
    out = OR(terms)
    if out < n or out != n + len(gates) - 1: gates.append([1, out, out])
    return gates if pair_ok_m(gates, mask) else None
def pair_ok_m(g, mk): return bank.pair_ok(g, mk, n, False)

T = json.load(open(TP)) if os.path.exists(TP) else {}
for mk in CL:
    k = str(mk)
    if k in T: continue
    r = {'g': [1, None], 'm': [1, None]}
    if mk == 0: r = {'g': [0, 0], 'm': [0, 0]}
    else:
        con = bank.rep_construction(mk, n, m) if kind == 'rep' else pair_construction(mk)
        if kind == 'pair' and not pair_monotone_possible(mk): r['m'] = [INF, INF]
        if con is not None:
            r['m'][1] = len(con); r['circ_m'] = con; r['g'][1] = len(con); r['circ_g'] = con
    T[k] = r

def save():
    tmp = TP + '.tmp'; json.dump(T, open(tmp, 'w')); os.replace(tmp, TP)
def tighten():
    for r in T.values():
        g, mm = r['g'], r['m']
        if mm[0] != INF and mm[0] < g[0]: mm[0] = g[0]
        if mm[1] is not None and mm[1] != INF and (g[1] is None or g[1] > mm[1]):
            g[1] = mm[1]
            if r.get('circ_m'): r['circ_g'] = r['circ_m']
def is_open(x): return x[1] is None or x[0] < x[1]

def run(jobs, budget):
    name = 'b2_%s_%d.txt' % (tag, int(time.time() * 1000))
    os.makedirs(os.path.join(DIR, 'care2'), exist_ok=True)
    with open(os.path.join(DIR, name), 'w', newline='\n') as f:
        for j, (k, mode, s) in enumerate(jobs):
            if kind == 'rep': spec = 'rel:%d:%x' % (n, int(k))
            else:
                cf = 'care2/%s_%s.txt' % (tag, k)
                if not os.path.exists(os.path.join(DIR, cf)):
                    with open(os.path.join(DIR, cf), 'w', newline='\n') as c: c.write(''.join('%d %d\n' % rw for rw in rows_of(int(k))))
                spec = 'care:%s/%s' % (WSL_DIR, cf)
            f.write('%d %d %s %d %d\n' % (j, NI, spec, s, 1 if mode == 'g' else 0))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'nice -n 15 bash ~/ns/explore_solve.sh %s/%s %d %d' % (WSL_DIR, name, budget, PAR)],
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
    st = {'SAT': 0, 'UNSAT': 0, 'other': 0}
    for (k, mode, s), (s_, gates) in res.items():
        x = T[k][mode]
        if s_ == 'SAT' and gates and ok(gates, int(k), mode == 'g'):
            if x[1] is None or s <= x[1]: x[1] = s; T[k]['circ_' + mode] = gates
            st['SAT'] += 1
        elif s_ == 'UNSAT':
            x[0] = max(x[0], s + 1); st['UNSAT'] += 1
        else: st['other'] += 1
    tighten(); save(); return st

def exact(): return sum(1 for r in T.values() for md in 'gm' if not is_open(r[md]))
tighten(); save()
log('start %s: %d classes, %d of %d values exact from constructions' % (tag, len(T), exact(), 2 * len(T)))
parked = set(); rnd = 0
while True:
    jobs = [(k, md, r[md][0]) for k, r in T.items() for md in 'gm' if is_open(r[md]) and (k, md) not in parked and r[md][0] < 40]
    if not jobs: break
    rnd += 1; t0 = time.time(); res = run(jobs, B1)
    for j, (s_, _) in res.items():
        if s_ not in ('SAT', 'UNSAT'): parked.add(j[:2])
    for j in jobs:
        if j not in res: parked.add(j[:2])
    st = apply(res)
    log('pass 1 round %d: %d jobs in %.0f s -> %s | exact %d of %d | parked %d' % (rnd, len(jobs), time.time() - t0, st, exact(), 2 * len(T), len(parked)))
# long budget for parked jobs: at lb, and above lb when no ub is known yet
tried = set()
while True:
    jobs = []
    for k, md in sorted(parked):
        x = T[k][md]
        if not is_open(x): continue
        for s in ([x[0]] + ([x[0] + d for d in (2, 4, 6)] if x[1] is None else [x[1] - 1])):
            if s >= x[0] and (x[1] is None or s < x[1]) and (k, md, s) not in tried: jobs.append((k, md, s)); tried.add((k, md, s))
    if not jobs: break
    t0 = time.time(); st = apply(run(jobs, B2))
    log('pass 2 (budget %d s): %d jobs in %.0f s -> %s | exact %d of %d' % (B2, len(jobs), time.time() - t0, st, exact(), 2 * len(T)))
    if st['SAT'] + st['UNSAT'] == 0: break
Bk = {k: {md: [r[md][0], r[md][1], r.get('circ_' + md)] for md in 'gm'} for k, r in T.items()}
json.dump(Bk, open(bank.path(kind, n, m), 'w'))
log('bank written: %s | exact %d of %d | with circuit %d' % (bank.path(kind, n, m), exact(), 2 * len(T),
    sum(1 for e in Bk.values() for md in 'gm' if e[md][2] is not None)))
