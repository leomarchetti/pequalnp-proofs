"""Symmetry classes for the answer bank, keyed exactly as bank.py looks them up.
  rep n m : n x m bipartite graphs up to row and column permutations (and transposition when n == m)
  pair n  : graphs on n vertices with optional single-vertex bits (bit n*i+j, i <= j) up to vertex permutations
Writes classes_<kind>_<n>x<m>.json: list of canonical masks (bank.rep_canon / bank.pair_canon form).
usage: python classes2.py rep n m | python classes2.py pair n"""
import itertools, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bank
kind = sys.argv[1]; t0 = time.time()
if kind == 'rep':
    n, m = int(sys.argv[2]), int(sys.argv[3])
    rperm = list(itertools.permutations(range(n)))
    def key(cols):   # cheap canonical: least sorted column tuple over row permutations
        best = None
        for p in rperm:
            t = tuple(sorted(sum(((c >> u) & 1) << p[u] for u in range(n)) for c in cols))
            if best is None or t < best: best = t
        return best
    seen = set(); reps = []
    for cols in itertools.combinations_with_replacement(range(1 << n), m):
        k = key(cols)
        if k in seen: continue
        seen.add(k)
        mask = sum(((c >> u) & 1) << (m * u + v) for v, c in enumerate(cols) for u in range(n))
        reps.append(mask)
    out = sorted({bank.rep_canon(mk, n, m)[0] for mk in reps})
    name = 'classes_rep_%dx%d.json' % (n, m)
else:
    n = int(sys.argv[2]); m = n
    perms = list(itertools.permutations(range(n)))
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    def gkey(edges):   # least sorted edge set over vertex permutations
        best = None
        for p in perms:
            t = tuple(sorted(tuple(sorted((p[i], p[j]))) for i, j in edges))
            if best is None or t < best: best = t
        return best
    simple = {}
    for bits in range(1 << len(pairs)):
        edges = [pairs[k] for k in range(len(pairs)) if (bits >> k) & 1]
        k = gkey(edges)
        if k not in simple: simple[k] = edges
    out = set()
    for edges in simple.values():
        base = sum(1 << (n * i + j) for i, j in edges)
        for L in range(1 << n):
            mk = base | sum(1 << (n * i + i) for i in range(n) if (L >> i) & 1)
            out.add(bank.pair_canon(mk, n)[0])
    out = sorted(out)
    name = 'classes_pair_%dx%d.json' % (n, n)
json.dump(out, open(os.path.join(bank.DIR, name), 'w'))
print('%s: %d classes in %.0f s -> %s' % (' '.join(sys.argv[1:]), len(out), time.time() - t0, name))
