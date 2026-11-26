"""Build and verify crown circuits (u != v) from the two-of plan of dp2.py.

usage: build.py n [EXTRA=val ...] [--out gates.txt]
Wires 0..n-1 are left vertices, n..2n-1 right vertices; gate j writes wire 2n+j.
Prints the size and whether the circuit represents the crown on all n*n one-each inputs.
"""
import sys, importlib.util, os
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('dp2', os.path.join(HERE, 'dp2.py'))
argv_backup = sys.argv
n = int(sys.argv[1]); extra = [a for a in sys.argv[2:] if '=' in a and not a.startswith('--')]
outp = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
sys.argv = ['dp2'] + extra
dp = importlib.util.module_from_spec(spec)
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(dp)
sys.argv = argv_backup

# exact base blocks (SAT): gate lists over local inputs 0..m-1, local gate k = wire m+k; last gate = Th2
BASE_T = {
    2: [(0, 0, 1)],
    3: [(0, 0, 1), (1, 0, 1), (1, 2, 3), (0, 4, 5)],
    4: [(1, 1, 2), (0, 3, 4), (1, 3, 4), (0, 0, 6), (0, 1, 2), (1, 7, 8), (1, 5, 9)],
    5: [(0, 2, 3), (1, 4, 5), (0, 1, 6), (1, 1, 6), (0, 0, 8), (1, 0, 8), (1, 2, 3), (1, 7, 9), (1, 11, 12), (0, 10, 13)],
}
gates = []
def g(op, a, b):
    gates.append((op, a, b)); return 2 * n + len(gates) - 1
def OR(a, b): return g(1, a, b)
def AND(a, b): return g(0, a, b)
def or_all(ws):
    w = ws[0]
    for x in ws[1:]: w = OR(w, x)
    return w

def th2(ws, needW):
    """returns (th2 wire or None, W wire or None)"""
    m = len(ws)
    if m == 1: return (None, ws[0])
    c, plan = dp.cost(m, needW)
    kind = plan[0]
    if kind in ('base', 'baseW'):
        if kind == 'baseW' and m == 2:
            return (AND(ws[0], ws[1]), OR(ws[0], ws[1]))
        loc = {i: ws[i] for i in range(m)}
        for k, (op, a, b) in enumerate(BASE_T[m]):
            loc[m + k] = g(op, loc[a], loc[b])
        t = loc[m + len(BASE_T[m]) - 1]
        return (t, or_all(ws) if needW else None)
    if kind == 'split':
        a = plan[1]
        tl, wl = th2(ws[:a], True); th, wh = th2(ws[a:], True)
        terms = [x for x in (tl, th) if x is not None] + [AND(wl, wh)]
        t = terms[0]
        for x in terms[1:]: t = OR(t, x)
        return (t, OR(wl, wh) if needW else None)
    if kind == 'grid':
        r, cc = plan[1], plan[2]
        rows = [cc] * r
        for i in range(r * cc - m): rows[-1 - i] -= 1
        cells, k = [], 0
        for i in range(r):
            cells.append(ws[k:k + rows[i]]); k += rows[i]
        rw = [or_all(row) for row in cells]
        cw = [or_all([cells[i][j] for i in range(r) if j < len(cells[i])]) for j in range(cc)]
        tr, wr = th2(rw, needW); tc, _ = th2(cw, False)
        return (OR(tr, tc), wr)
    if kind == 'alone':
        t0, w0 = th2(ws[:-1], True); z = ws[-1]
        t = AND(z, w0)
        if t0 is not None: t = OR(t0, t)
        return (t, OR(w0, z) if needW else None)
    raise ValueError(plan)

w = [OR(i, n + i) for i in range(n)]
out, _ = th2(w, False)
assert out == 2 * n + len(gates) - 1

# verify on relations: bit u*n+v
row = [sum(1 << (u * n + v) for v in range(n)) for u in range(n)]
col = [sum(1 << (u * n + v) for u in range(n)) for v in range(n)]
val = row + col
for op, a, b in gates:
    val.append(val[a] & val[b] if op == 0 else val[a] | val[b])
target = sum(1 << (u * n + v) for u in range(n) for v in range(n) if u != v)
print(f'n={n} size={len(gates)} represents_crown={val[-1] == target}')
if outp:
    with open(outp, 'w') as f:
        for op, a, b in gates: f.write(f'{op} {a} {b}\n')
