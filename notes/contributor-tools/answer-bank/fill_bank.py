"""Build bank_rep_<n>x<n>.json from table_<n>.json (explore.py): every class keeps its proven [lb, ub] per mode and a
circuit of size ub. Circuits come from the table when explore.py stored one, else from the row/column construction
when that reaches ub, else from one solver run at size ub (finding a circuit of a size known to work is the fast way
round). Run it only when explore.py is not writing the same table.
usage: python fill_bank.py n [budget_seconds]"""
import json, os, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bank
n = int(sys.argv[1]); budget = int(sys.argv[2]) if len(sys.argv) > 2 else 60
DIR = bank.DIR; WSL_DIR = '/mnt/c/<path-to-checkout>/.pnp/explore'
T = json.load(open(os.path.join(DIR, 'table_%d.json' % n)))
B = {}
need = []
for k, r in T.items():
    mask = r['mask']; e = {}
    con = bank.rep_construction(mask, n, n)
    for mode in ('g', 'm'):
        lb, ub = r[mode]
        circ = r.get('circ_' + mode)
        if circ is None and con is not None and len(con) == ub: circ = con
        if circ is not None and not bank.rep_ok(circ, mask, n, n, mode == 'g'): circ = None
        e[mode] = [lb, ub, circ]
        if circ is None and ub and ub > 0: need.append((str(mask), mode, ub))
    B[str(mask)] = e
print('%dx%d: %d classes; circuits from the table or the construction: %d; to solve: %d'
      % (n, n, len(T), sum(1 for e in B.values() for md in 'gm' if e[md][2] is not None), len(need)), flush=True)
if need:
    name = 'fill_%d.txt' % int(time.time())
    with open(os.path.join(DIR, name), 'w', newline='\n') as f:
        for j, (mk, mode, s) in enumerate(need): f.write('%d %d rel:%d:%x %d %d\n' % (j, 2 * n, n, int(mk), s, 1 if mode == 'g' else 0))
    p = subprocess.Popen(['wsl.exe', '-e', 'bash', '-lc', 'nice -n 10 bash ~/ns/explore_solve.sh %s/%s %d 8' % (WSL_DIR, name, budget)],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    got = 0
    for line in p.stdout:
        f = line.split()
        if len(f) >= 4 and f[0] == 'RES' and f[2] == 'SAT':
            mk, mode, s = need[int(f[1])]
            gates = [[int(x) for x in t.split(',')] for t in f[3].split(';') if t]
            if bank.rep_ok(gates, int(mk), n, n, mode == 'g'): B[mk][mode][2] = gates; got += 1
    p.wait(); os.remove(os.path.join(DIR, name))
    print('solved %d of %d' % (got, len(need)), flush=True)
json.dump(B, open(bank.path('rep', n, n), 'w'))
have = sum(1 for e in B.values() for md in 'gm' if e[md][2] is not None or e[md][1] == 0)
print('bank written: %s | entries with a circuit (or size 0): %d of %d' % (bank.path('rep', n, n), have, 2 * len(B)))
