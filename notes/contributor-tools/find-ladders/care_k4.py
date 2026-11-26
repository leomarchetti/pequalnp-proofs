"""Care rows for monotone synthesis of f = 'contains one of the minterm sets' on n inputs.
A monotone circuit equals f iff it is true on every minterm and false on every maximal false point.
usage: care_k4.py out.txt   (writes 'row value' lines; row = bitmask with input i = bit i)
"""
import sys, itertools
n = 10
MIN = [{4, 5, 6, 7, 8, 9}, {0, 2, 3, 5, 6, 9}, {0, 1, 3, 4, 6, 8}, {0, 1, 2, 4, 5, 7}, {1, 2, 3, 7, 8, 9}]
mins = [sum(1 << i for i in s) for s in MIN]
f = lambda r: any(r & m == m for m in mins)
false_pts = [r for r in range(1 << n) if not f(r)]
maxfalse = [r for r in false_pts if all(f(r | (1 << i)) for i in range(n) if not r >> i & 1)]
with open(sys.argv[1], 'w') as fo:
    for r in mins: fo.write(f'{r} 1\n')
    for r in maxfalse: fo.write(f'{r} 0\n')
print('minterms', len(mins), 'maximal false points', len(maxfalse))
