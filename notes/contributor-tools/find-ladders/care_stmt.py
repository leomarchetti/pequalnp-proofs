"""Care rows for a monotone desk FIND statement `HasCircuitSize n (fun x => DNF) s`.
Minterms = the minimal true points, maximal false points = the maximal false points (brute force).
usage: care_stmt.py gaps.json GAP_ID out.txt
"""
import json, re, sys
gaps, gid, out = sys.argv[1:4]
g = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}[gid]
stmt = g['statement'].strip()
m = re.match(r'PEqualNP\.MetaComplexity\.HasCircuitSize (\d+) \(fun x : Fin \d+ → Bool => (.*)\) (\d+)$', stmt, re.S)
n, expr, s = int(m.group(1)), m.group(2), int(m.group(3))
py = re.sub(r'\bx (\d+)', r'x[\1]', expr).replace('&&', ' and ').replace('||', ' or ').replace('!', ' not ')
f = eval('lambda x: bool(' + py + ')')
tt = [f([(r >> i) & 1 == 1 for i in range(n)]) for r in range(1 << n)]
mono = all(not tt[r] or tt[r | (1 << i)] for r in range(1 << n) for i in range(n))
if not mono: raise SystemExit('not monotone (care rows need a monotone function)')
mins = [r for r in range(1 << n) if tt[r] and all(not tt[r & ~(1 << i)] for i in range(n) if r >> i & 1)]
maxf = [r for r in range(1 << n) if not tt[r] and all(tt[r | (1 << i)] for i in range(n) if not r >> i & 1)]
with open(out, 'w') as fo:
    for r in mins: fo.write(f'{r} 1\n')
    for r in maxf: fo.write(f'{r} 0\n')
print(gid, 'n', n, 'bound', s, 'minterms', len(mins), 'maximal false', len(maxf))
