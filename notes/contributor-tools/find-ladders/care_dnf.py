"""Care rows for a monotone function given by its minterms (inputs 0..n-1).
usage: care_dnf.py n 'a,b,c;d,e,f;...' out.txt
"""
import sys
n = int(sys.argv[1])
mins_sets = [[int(t) for t in m.split(',')] for m in sys.argv[2].split(';')]
mins = [sum(1 << i for i in s) for s in mins_sets]
f = lambda r: any(r & m == m for m in mins)
maxf = [r for r in range(1 << n) if not f(r) and all(f(r | (1 << i)) for i in range(n) if not r >> i & 1)]
with open(sys.argv[3], 'w') as fo:
    for r in mins: fo.write(f'{r} 1\n')
    for r in maxf: fo.write(f'{r} 0\n')
print('n', n, 'minterms', len(mins), 'maximal false', len(maxf))
