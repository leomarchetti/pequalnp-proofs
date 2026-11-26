"""Exact synthesis of a MULTI-OUTPUT monotone AND/OR fan-in-2 circuit by SAT on a few rows.

usage: synth_multi.py SPEC S cadical workdir [secs]
SPEC:  enc:N       N one-hot inputs, outputs = the log2(N) bits of the hot index
       encneg:N    same plus the negated bits (outputs 0..k-1 bits, k..2k-1 negated bits)
Rows are the N one-hot inputs. Each output picks any wire (input or gate). Every gate is read
by a later gate or is an output. Colex symmetry breaking as in synth_sat3.py.
Prints SAT/UNSAT/UNKNOWN; on SAT: gate lines 'op a b' (0 AND, 1 OR), then 'out v w' lines.
"""
import os, sys, subprocess, time

spec = sys.argv[1]; S = int(sys.argv[2]); cad = sys.argv[3]; wd = sys.argv[4]
secs = int(sys.argv[5]) if len(sys.argv) > 5 else 0
kind, N = spec.split(':'); N = int(N); n = N
k = N.bit_length() - 1
rows = list(range(N))                    # row p: input p hot
targets = [[(p >> v) & 1 for p in rows] for v in range(k)]
if kind == 'encneg':
    targets += [[1 - ((p >> v) & 1) for p in rows] for v in range(k)]
O = len(targets)

nv = 0
def new():
    global nv
    nv += 1
    return nv
cls = []
W = n + S
TRUE = new(); cls.append([TRUE])
A = [[None] * W for _ in range(S)]; B = [[None] * W for _ in range(S)]
Age = [[None] * (W + 1) for _ in range(S)]; Bge = [[None] * (W + 1) for _ in range(S)]
isand = [new() for _ in range(S)]
def exactly_one(vs):
    cls.append(vs)
    for x in range(len(vs)):
        for y in range(x + 1, len(vs)):
            cls.append([-vs[x], -vs[y]])
for j in range(S):
    w = n + j
    for kk in range(w):
        A[j][kk] = new(); B[j][kk] = new()
    exactly_one(A[j][:w]); exactly_one(B[j][:w])
    for G, sel in ((Age, A), (Bge, B)):
        for kk in range(w + 1):
            G[j][kk] = new()
        cls.append([G[j][0]]); cls.append([-G[j][w]])
        for kk in range(w):
            cls.append([-G[j][kk], G[j][kk + 1], sel[j][kk]])
            cls.append([G[j][kk], -G[j][kk + 1]])
            cls.append([G[j][kk], -sel[j][kk]])
    for kk in range(w):
        cls.append([-A[j][kk], Bge[j][kk + 1]])
val_ = {}
def wl(w, r):
    if w < n:
        return TRUE if w == r else -TRUE
    return val_[(w - n, r)]
for j in range(S):
    for r in rows:
        val_[(j, r)] = new()
for j in range(S):
    w = n + j
    for r in rows:
        x = val_[(j, r)]; L = new(); R = new()
        for kk in range(w):
            v = wl(kk, r)
            cls.append([-A[j][kk], -v, L]); cls.append([-A[j][kk], v, -L])
            cls.append([-B[j][kk], -v, R]); cls.append([-B[j][kk], v, -R])
        t = isand[j]
        cls.append([-t, -x, L]); cls.append([-t, -x, R]); cls.append([-t, x, -L, -R])
        cls.append([t, x, -L]); cls.append([t, x, -R]); cls.append([t, -x, L, R])
# outputs: each picks a wire whose column equals its target
OUT = [[new() for _ in range(W)] for _ in range(O)]
for o in range(O):
    exactly_one(OUT[o])
    for wv in range(W):
        for r in rows:
            v = wl(wv, r)
            cls.append([-OUT[o][wv], v] if targets[o][r] else [-OUT[o][wv], -v])
# every gate read later or an output
for j in range(S):
    lits = [l for jj in range(j + 1, S) for l in (A[jj][n + j], B[jj][n + j])]
    lits += [OUT[o][n + j] for o in range(O)]
    cls.append(lits)
# colex order for consecutive gates not reading each other
for j in range(S - 1):
    j2 = j + 1; rd = [A[j2][n + j], B[j2][n + j]]
    w1 = n + j
    for kk in range(w1 + 1):
        cls.append([-Bge[j][kk], Bge[j2][kk]] + rd)
    for p in range(w1):
        for kk in range(w1 + 1):
            cls.append([-B[j][p], -B[j2][p], -Age[j][kk], Age[j2][kk]] + rd)

os.makedirs(wd, exist_ok=True)
tag = os.environ.get('TAG', '') + '%s%d_%d' % (kind, N, S)
cnf = os.path.join(wd, tag + '.cnf')
with open(cnf, 'w') as f:
    f.write('p cnf %d %d\n' % (nv, len(cls)))
    for c in cls:
        f.write(' '.join(map(str, c)) + ' 0\n')
t0 = time.time()
cmd = [cad, '-q', '--modelalllits=true', cnf] + (['-t', str(secs)] if secs else [])
out = subprocess.run(cmd, capture_output=True, text=True).stdout
el = time.time() - t0
if 's UNSATISFIABLE' in out:
    print('UNSAT', tag, 'vars', nv, 'clauses', len(cls), '%.1fs' % el); sys.exit(0)
if 's SATISFIABLE' not in out:
    print('UNKNOWN', tag, '%.1fs' % el); sys.exit(0)
true = set()
for line in out.splitlines():
    if line.startswith('v '):
        for t in line[2:].split():
            v = int(t)
            if v > 0: true.add(v)
print('SAT', tag, 'vars', nv, 'clauses', len(cls), '%.1fs' % el)
for j in range(S):
    w = n + j
    a = next(kk for kk in range(w) if A[j][kk] in true)
    b = next(kk for kk in range(w) if B[j][kk] in true)
    print(0 if isand[j] in true else 1, a, b)
for o in range(O):
    print('out', o, next(wv for wv in range(W) if OUT[o][wv] in true))
