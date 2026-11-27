"""Enumerate n x n 0/1 matrices (bipartite graphs, bit k*u+v = edge (u,v)) up to row permutations, column permutations
and transposition. Writes classes_<n>.json: [{"mask": canonical mask, "orbit": size, "comp": class index of the
complement}], canonical = least mask over the symmetry group.
usage: python classes.py n"""
import itertools, json, sys
n = int(sys.argv[1]); N = n * n
perms = list(itertools.permutations(range(n)))
def rows_of(mask): return [(mask >> (n * u)) & ((1 << n) - 1) for u in range(n)]
def from_rows(rs): return sum(r << (n * u) for u, r in enumerate(rs))
def tr(mask): return sum(((mask >> (n * u + v)) & 1) << (n * v + u) for u in range(n) for v in range(n))
colmap = {}
def permute_cols(r, p):   # new column p[v] gets old column v
    out = 0
    for v in range(n):
        if (r >> v) & 1: out |= 1 << p[v]
    return out
pc = [[permute_cols(r, p) for r in range(1 << n)] for p in perms]
def canon(mask):
    best = None
    for m in (mask, tr(mask)):
        rs = rows_of(m)
        for t in pc:
            c = from_rows(sorted(t[r] for r in rs))   # row permutation = sort rows (rows-as-ints sorted ascending)
            if best is None or c < best: best = c
    return best
seen = {}
# every class has a representative with sorted rows; enumerate sorted row tuples
for rs in itertools.combinations_with_replacement(range(1 << n), n):
    c = canon(from_rows(rs))
    if c not in seen: seen[c] = 0
classes = sorted(seen)
idx = {c: i for i, c in enumerate(classes)}
full = (1 << N) - 1
out = [{'mask': c, 'comp': idx[canon(full ^ c)]} for c in classes]
json.dump(out, open('classes_%d.json' % n, 'w'))
print(n, 'classes:', len(classes), '| self-complementary:', sum(1 for i, o in enumerate(out) if o['comp'] == i))
