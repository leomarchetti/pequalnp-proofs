"""Cost model for 'two of m wires, at most two on' (Th2) with an optional OR-of-all output (W).
crown(n) = n (one OR per index: w_i = x_i | y_i) + cost(n, needW=False).
Plans: exact SAT base blocks, split, grid (row/col ORs), one item alone.
"""
import functools, math, sys

TB = {1: 0, 2: 1, 3: 4, 4: 7, 5: 10}        # exact Th2 sizes (SAT), no W output
TWB = {1: 0, 2: 2, 3: 5, 4: 8, 5: 11}       # exact Th2+W sizes (SAT-verified minima)
if len(sys.argv) > 1:                       # extra exact values, e.g. TW3=5 T6=13
    for a in sys.argv[1:]:
        k, v = a.split('=')
        (TWB if k.startswith('TW') else TB)[int(k.lstrip('TW'))] = int(v)

@functools.lru_cache(None)
def cost(m, needW):
    best = (10**9, None)
    def consider(c, plan):
        nonlocal best
        if c < best[0]: best = (c, plan)
    if m <= 1:
        return (0, ('leaf',))
    if needW and m in TWB: consider(TWB[m], ('baseW', m))
    if m in TB: consider(TB[m] + ((m - 1) if needW else 0), ('base', m))
    for a in range(1, m // 2 + 1):
        b = m - a
        ca = cost(a, True)[0]; cb = cost(b, True)[0]
        terms = (a >= 2) + (b >= 2) + 1
        consider(ca + cb + 1 + (terms - 1) + (1 if needW else 0), ('split', a, b))
    for r in range(2, m):
        c = math.ceil(m / r)
        if c < 2 or (r - 1) * c >= m: continue
        rows = [c] * r
        for i in range(r * c - m): rows[-1 - i] -= 1
        if min(rows) < 1: continue
        cols = [sum(1 for k in rows if k > j) for j in range(c)]
        ccost = sum(k - 1 for k in rows) + sum(k - 1 for k in cols) + cost(r, needW)[0] + cost(c, False)[0] + 1
        consider(ccost, ('grid', r, c))
    consider(cost(m - 1, True)[0] + 2 + (1 if needW else 0), ('alone', m - 1))
    # tri: three partitions, every item in exactly two of them (types 12, 13, 23);
    # two-of inside each partition, plus (any P1) & (any P2) & (any P3) for different-type pairs
    for k1 in range(1, m):
        for k2 in range(k1, m):
            for k3 in range(k2, m):
                if k1 * k2 + k1 * k3 + k2 * k3 < m: continue
                if k1 + k2 + k3 > m: break
                parts = (k1, k2, k3)
                c = 2 * m - sum(parts) + sum(cost(k, True)[0] for k in parts) + 2
                terms = sum(1 for k in parts if k >= 2) + 1
                c += (terms - 1) + (1 if needW else 0)
                consider(c, ('tri', k1, k2, k3))
    return best

def show(m, needW, depth=0):
    c, plan = cost(m, needW)
    out = '  ' * depth + f'{m}{"+W" if needW else ""}: {c} {plan}'
    print(out)
    if plan[0] == 'split': show(plan[1], True, depth + 1); show(plan[2], True, depth + 1)
    if plan[0] == 'grid':
        show(plan[1], needW, depth + 1); show(plan[2], False, depth + 1)
    if plan[0] == 'alone': show(plan[1], True, depth + 1)
    if plan[0] == 'tri':
        for k in plan[1:]: show(k, True, depth + 1)

targets = {13: 44, 15: 51, 16: 54, 17: 58, 26: 89, 5: 15, 6: 18}
for n in [5, 6, 13, 15, 16, 17, 26]:
    c = n + cost(n, False)[0]
    print(f'n={n}: crown {c}  target {targets[n]}  {"OK" if c <= targets[n] else "over by " + str(c - targets[n])}')
print()
show(13, False)
