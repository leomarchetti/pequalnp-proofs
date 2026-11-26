"""Exact synthesis of AND/OR(/NOT) fan-in-2 circuits by SAT, compact encoding.

usage: synth_sat3.py n SPEC S allow_not cadical workdir [secs]
SPEC: care:file ('row value' lines) | hex:<truth table> | rel:nl:<hex>  (one vertex on each side)
Gate j writes wire n+j and picks its inputs with two one-hot selectors (left a < right b), with
order-encoded helpers. Symmetry breaking (all valid for UNSAT claims):
  - every gate but the last is read later;
  - colex order: if gate j+1 does not read gate j then (b, a) of gate j+1 >= (b, a) of gate j;
  - optional PSYM='and:0-1,or:0-7': some gate is one of these (see find-ladders/README.md).
Prints SAT/UNSAT/UNKNOWN, then on SAT the gate list as 'op a b' (0 AND, 1 OR, 2 NOT b=-1).
"""
import os, sys, subprocess, time

n = int(sys.argv[1]); spec = sys.argv[2]; S = int(sys.argv[3]); allow_not = sys.argv[4] == '1'
cad = sys.argv[5]; wd = sys.argv[6]; secs = int(sys.argv[7]) if len(sys.argv) > 7 else 0

rows = []  # (assignment bitmask over inputs, wanted value)
kind, _, val = spec.partition(':')
if kind == 'care':
    for line in open(val):
        r, v = line.split(); rows.append((int(r), int(v)))
elif kind == 'hex':
    tt = int(val, 16)
    rows = [(r, (tt >> r) & 1) for r in range(1 << n)]
elif kind == 'rel':
    nl_s, hx = val.split(':'); nl = int(nl_s); A = int(hx, 16); nr = n - nl
    for u in range(nl):
        for v in range(nr):
            rows.append(((1 << u) | (1 << (nl + v)), (A >> (u * nr + v)) & 1))
else:
    raise SystemExit('bad spec')

nv = 0
def new():
    global nv
    nv += 1
    return nv
cls = []
W = n + S
TRUE = new(); cls.append([TRUE])

# selectors
A = [[None] * W for _ in range(S)]; B = [[None] * W for _ in range(S)]
Age = [[None] * (W + 1) for _ in range(S)]; Bge = [[None] * (W + 1) for _ in range(S)]
isand = [new() for _ in range(S)]
isnot = [new() if allow_not else None for _ in range(S)]
for j in range(S):
    w = n + j
    for k in range(w):
        A[j][k] = new(); B[j][k] = new()
    for sel in (A[j], B[j]):
        vs = sel[:w]; cls.append(vs)
        for x in range(len(vs)):
            for y in range(x + 1, len(vs)):
                cls.append([-vs[x], -vs[y]])
    # order helpers: Age[j][k] <-> left index >= k  (k = 0..w); same for right
    for G, sel in ((Age, A), (Bge, B)):
        for k in range(w + 1):
            G[j][k] = new()
        cls.append([G[j][0]]); cls.append([-G[j][w]])
        for k in range(w):
            # G[k] <-> G[k+1] or sel[k]
            cls.append([-G[j][k], G[j][k + 1], sel[j][k]])
            cls.append([G[j][k], -G[j][k + 1]])
            cls.append([G[j][k], -sel[j][k]])
    if allow_not:
        cls.append([-isnot[j], -isand[j]])          # NOT gates have isand = 0
        # NOT: right selector equals left selector; binary: left < right
        for k in range(w):
            cls.append([-isnot[j], -A[j][k], B[j][k]])
            cls.append([isnot[j], -A[j][k], Bge[j][k + 1]])
    else:
        for k in range(w):
            cls.append([-A[j][k], Bge[j][k + 1]])

def reads(jj, j):
    """literals saying gate jj reads gate j"""
    return [A[jj][n + j], B[jj][n + j]]

# semantics
val_ = {}
def wl(w, r):
    if w < n:
        return TRUE if (r >> w) & 1 else -TRUE
    return val_[(w - n, r)]
for j in range(S):
    for (r, _) in rows:
        val_[(j, r)] = new()
for j in range(S):
    w = n + j
    for (r, _) in rows:
        x = val_[(j, r)]; L = new(); R = new()
        for k in range(w):
            v = wl(k, r)
            cls.append([-A[j][k], -v, L]); cls.append([-A[j][k], v, -L])
            cls.append([-B[j][k], -v, R]); cls.append([-B[j][k], v, -R])
        t = isand[j]
        nt = isnot[j]
        # AND
        cls.append([-t, -x, L]); cls.append([-t, -x, R]); cls.append([-t, x, -L, -R])
        if allow_not:
            # OR when neither AND nor NOT
            cls.append([t, nt, x, -L]); cls.append([t, nt, x, -R]); cls.append([t, nt, -x, L, R])
            cls.append([-nt, x, L]); cls.append([-nt, -x, -L])
        else:
            cls.append([t, x, -L]); cls.append([t, x, -R]); cls.append([t, -x, L, R])
for (r, want) in rows:
    x = val_[(S - 1, r)]
    cls.append([x] if want else [-x])
# every non-output gate read later
for j in range(S - 1):
    cls.append([l for jj in range(j + 1, S) for l in reads(jj, j)])
# colex order of (right, left) for consecutive gates not reading each other
for j in range(S - 1):
    j2 = j + 1; rd = reads(j2, j)
    w1 = n + j
    for k in range(w1 + 1):
        # right(j) >= k  ->  right(j2) >= k
        cls.append([-Bge[j][k], Bge[j2][k]] + rd)
    for p in range(w1):
        for k in range(w1 + 1):
            # right equal p and left(j) >= k -> left(j2) >= k
            cls.append([-B[j][p], -B[j2][p], -Age[j][k], Age[j2][k]] + rd)
if os.environ.get('PSYM'):
    gs = []
    for it in os.environ['PSYM'].split(','):
        kk, ab = it.split(':'); a0, b0 = map(int, ab.split('-'))
        for j in range(S):
            g = new(); gs.append(g)
            cls.append([-g, A[j][a0]]); cls.append([-g, B[j][b0]])
            cls.append([-g, isand[j]] if kk == 'and' else [-g, -isand[j]])
            if allow_not: cls.append([-g, -isnot[j]])
    cls.append(gs)

os.makedirs(wd, exist_ok=True)
tag = os.environ.get('TAG', '') + '%s_%d_%d_%d' % (spec.replace(':', '').replace('/', '')[:24], n, S, int(allow_not))
cnf = os.path.join(wd, tag + '.cnf')
with open(cnf, 'w') as f:
    f.write('p cnf %d %d\n' % (nv, len(cls)))
    for c in cls:
        f.write(' '.join(map(str, c)) + ' 0\n')
t0 = time.time()
cmd = [cad, '-q', '--modelalllits=true', cnf] + (['-t', str(secs)] if secs else [])
p = subprocess.run(cmd, capture_output=True, text=True)
el = time.time() - t0
out = p.stdout
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
    a = next(k for k in range(w) if A[j][k] in true)
    b = next(k for k in range(w) if B[j][k] in true)
    if allow_not and isnot[j] in true:
        print(2, a, -1)
    else:
        print(0 if isand[j] in true else 1, a, b)
