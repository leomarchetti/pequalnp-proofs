"""Check the four conjectures against a cost table (table_<n>.json from explore.py). Only proven facts count:
a gap is proven when lb of one side minus ub of the other exceeds the bound; a gap is still possible when ub minus lb does.
  19037: m(A) <= m(comp A) + 2n          (a break needs m(A) - m(comp) > 2n)
  19385: some A has m(A) > m(comp A) + 2n - 4
  19158: m(A) <= g(A) + 2n - 5            (19159 is its break: m(A) > g(A) + 2n - 5)
usage: python check.py n"""
import json, sys, collections
n = int(sys.argv[1]); T = json.load(open('table_%d.json' % n))
exact = lambda x: x[1] is not None and x[0] >= x[1]
done = sum(1 for r in T.values() for m in ('g', 'm') if exact(r[m]))
print('%dx%d: %d classes, exact values for %d of %d (class, mode) pairs' % (n, n, len(T), done, 2 * len(T)))
def report(name, bound, side):
    proven, possible, best = [], [], None
    for k, r in T.items():
        a = r['m']; b = T[str(r['comp'])]['m'] if side == 'comp' else r['g']
        if a[1] is None or b[1] is None: continue
        lo, hi = a[0] - b[1], a[1] - b[0]          # the gap is proven >= lo and is at most hi
        if best is None or lo > best[0]: best = (lo, k)
        if lo > bound: proven.append((lo, k))
        elif hi > bound: possible.append((hi, k))
    print('  %-34s bound %2d | largest proven gap %s (class %s) | breaks proven: %d | classes where a break is still possible: %d'
          % (name, bound, best[0] if best else '-', best[1] if best else '-', len(proven), len(possible)))
    return proven, possible
report('19037 m(A) - m(comp) <= 2n', 2 * n, 'comp')
report('19385 m(A) - m(comp) > 2n-4 ?', 2 * n - 4, 'comp')
report('19158 m(A) - g(A) <= 2n-5', 2 * n - 5, 'g')
dist = collections.Counter((r['g'][1], r['m'][1]) for r in T.values() if exact(r['g']) and exact(r['m']))
print('  (g, m) value pairs among exact classes:', sorted(dist.items())[:40])
