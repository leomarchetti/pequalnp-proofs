"""Exact synthesis by SAT: fan-in-2 AND/OR (+ optional NOT1) circuits for an n-input table.

usage: synth_sat.py <n> <table: 'maj:K' | 'hex:<bits>' | 'int:<u>'> <size> <allowNot 0/1> <cadical> <workdir> [seconds]
Wires 0..n-1 are inputs (row r: input i = bit i of r); gate j writes wire n+j; output = last gate.
Constraints: exactly one option per gate (AND pair, OR pair, NOT single); every non-output gate is
read later; no NOT reads a NOT; consecutive-gate canonical order (gate j+1 reads gate j or has a
larger option index). Prints SAT + gate list (verified by simulation) / UNSAT / UNKNOWN.
"""
import sys, os, subprocess, itertools, time, gc

def main():
    n = int(sys.argv[1]); spec = sys.argv[2]; S = int(sys.argv[3]); allow_not = sys.argv[4] == '1'
    cad = sys.argv[5]; wd = sys.argv[6]; secs = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    R = 1 << n
    kind, val = spec.split(':', 1)
    rows = list(range(R))
    if kind == 'rel':
        # rel:<nl>:<hex relation bit u*m+v>; n = nl + m inputs; rows = one vertex each side
        nl_s, hx = val.split(':'); nl = int(nl_s); m = n - nl; A = int(hx, 16)
        rows = []; tt = [0] * R
        for u in range(nl):
            for v in range(m):
                r = (1 << u) | (1 << (nl + v)); rows.append(r); tt[r] = (A >> (u * m + v)) & 1
    elif kind == 'th2p':
        rows = [r for r in range(R) if bin(r).count('1') <= 2]; tt = [0] * R
        for r in rows: tt[r] = 1 if bin(r).count('1') == 2 else 0
    elif kind == 'care':
        # care:<file> with lines 'row value'; only those rows are constrained
        rows = []; tt = [0] * R
        for line in open(val):
            r, v = line.split(); r = int(r); rows.append(r); tt[r] = int(v)
    elif kind == 'maj':
        K = int(val); tt = [1 if bin(r).count('1') >= K else 0 for r in range(R)]
    elif kind == 'int':
        u = int(val); tt = [(u >> r) & 1 for r in range(R)]
    else:
        u = int(val, 16); tt = [(u >> r) & 1 for r in range(R)]
    nv = [0]; cls = []
    def new():
        nv[0] += 1; return nv[0]
    TRUE = new(); cls.append([TRUE])
    def lit_input(i, r):
        return TRUE if (r >> i) & 1 else -TRUE
    W = n + S
    val_ = {}  # (gate j, row r) -> var
    for j in range(S):
        for r in rows:
            val_[(j, r)] = new()
    def wl(w, r):
        return lit_input(w, r) if w < n else val_[(w - n, r)]
    opts = []  # per gate: list of (var, kind, a, b)
    for j in range(S):
        o = []
        wires = n + j
        for b in range(wires):
            for a in range(b):
                o.append((new(), 'and', a, b)); o.append((new(), 'or', a, b))
        if allow_not:
            for a in range(wires):
                o.append((new(), 'not', a, -1))
        opts.append(o)
        vs = [v for v, *_ in o]
        cls.append(vs)
        # at most one: sequential counter (ladder)
        prev = None
        for idx, v in enumerate(vs):
            if idx < len(vs) - 1:
                s = new()
                cls.append([-v, s])
                if prev is not None:
                    cls.append([-prev, s]); cls.append([-v, -prev])
                prev = s
            else:
                if prev is not None:
                    cls.append([-v, -prev])
    # semantics
    for j in range(S):
        for (v, k, a, b) in opts[j]:
            for r in rows:
                x = val_[(j, r)]; A = wl(a, r)
                if k == 'not':
                    cls.append([-v, -x, -A]); cls.append([-v, x, A])
                else:
                    B = wl(b, r)
                    if k == 'and':
                        cls.append([-v, -x, A]); cls.append([-v, -x, B]); cls.append([-v, x, -A, -B])
                    else:
                        cls.append([-v, x, -A]); cls.append([-v, x, -B]); cls.append([-v, -x, A, B])
    # output
    for r in rows:
        x = val_[(S - 1, r)]
        cls.append([x] if tt[r] else [-x])
    if os.environ.get('OR_ALL') == '1':
        # some gate must equal the OR of all inputs on the care rows
        orall = []
        for j in range(S):
            v = new(); orall.append(v)
            for r in rows:
                want = 1 if r != 0 else 0
                x = val_[(j, r)]
                cls.append([-v, x] if want else [-v, -x])
        cls.append(orall)
    # every non-output gate read later (skipped when a second output, the OR-of-all, is required:
    # that gate is legitimately unread; dead gates can only add size, so this stays exact)
    for j in (range(S - 1) if os.environ.get('OR_ALL') != '1' else []):
        w = n + j; readers = []
        for jj in range(j + 1, S):
            for (v, k, a, b) in opts[jj]:
                if a == w or b == w:
                    readers.append(v)
        cls.append(readers)
    # no NOT reads a NOT
    if allow_not:
        isnot = []
        for j in range(S):
            nots = [v for (v, k, a, b) in opts[j] if k == 'not']
            isnot.append(nots)
        for j in range(S):
            for (v, k, a, b) in opts[j]:
                if k == 'not' and a >= n:
                    for u in isnot[a - n]:
                        cls.append([-v, -u])
    # canonical order: gate j+1 reads gate j, or its option index > gate j's option index
    # implemented as: for options p of gate j and q of gate j+1 with q not reading wire n+j and
    # key(q) <= key(p): not both.  key = (kind, a, b) ordering via tuple.
    def key(o):
        return ({'and': 0, 'or': 1, 'not': 2}[o[1]], o[2], o[3])
    for j in range(S - 1):
        A_ = sorted(opts[j], key=key); B_ = opts[j + 1]
        for q in B_:
            if q[2] == n + j or q[3] == n + j:
                continue
            kq = key(q)
            for p in A_:
                if key(p) >= kq:
                    cls.append([-p[0], -q[0]])
    # optional symmetry breaking for functions symmetric in all inputs and self-dual
    # (e.g. majority): some gate is AND(x0, x1) or NOT(x0).  Valid because the first gate
    # reads only inputs; relabel them to 0,1 (or 0) and dualize AND<->OR if needed.
    # monotone symmetric targets (e.g. two-of under a promise): some gate is AND(x0,x1) or OR(x0,x1)
    if os.environ.get('SYMM') == '1':
        cls.append([v for j in range(S) for (v, k, a, b) in opts[j]
                    if k in ('and', 'or') and a == 0 and b == 1])
    # crown-type relations, symmetric under index permutations and left/right swap:
    # some gate combines (x0,y0), (x0,x1) or (x0,y1)  [left inputs 0..nl-1, right inputs nl..]
    if os.environ.get('RSYM') == '1':
        nlr = int(os.environ['RSYM_NL'])
        pairs = {(0, nlr), (0, 1), (0, nlr + 1)}
        cls.append([v for j in range(S) for (v, k, a, b) in opts[j]
                    if k in ('and', 'or') and (a, b) in pairs])
    # generic symmetry breaking: PSYM='and:0-1,or:0-7' requires some gate to be one of these
    # (valid when every pair of distinct inputs maps to a listed pair under a symmetry of f)
    if os.environ.get('PSYM'):
        want = set()
        for it in os.environ['PSYM'].split(','):
            kk, ab = it.split(':'); a0, b0 = ab.split('-'); want.add((kk, int(a0), int(b0)))
        cls.append([v for j in range(S) for (v, k, a, b) in opts[j] if (k, a, b) in want])
    if os.environ.get('SYM') == '1':
        cls.append([v for j in range(S) for (v, k, a, b) in opts[j]
                    if (k == 'and' and a == 0 and b == 1) or (k == 'not' and a == 0)])
    os.makedirs(wd, exist_ok=True)
    tag = os.environ.get('TAG', '') + '%s_%d_%d_%d' % (spec.replace(':', '')[:24], n, S, int(allow_not))
    seed = os.environ.get('SEED')
    if seed:
        tag += '_s' + seed
    cnf = os.path.join(wd, tag + '.cnf')
    with open(cnf, 'w') as f:
        f.write('p cnf %d %d\n' % (nv[0], len(cls)))
        for c in cls:
            f.write(' '.join(map(str, c)) + ' 0\n')
    # Free the clause list before solving: a waiting encoder keeps only the small option map.
    ncls = len(cls); del cls; val_.clear(); gc.collect()
    t0 = time.time()
    cmd = [cad, '-q'] + (['--seed=' + seed] if seed else []) + [cnf] + (['-t', str(secs)] if secs else [])
    outp = os.path.join(wd, tag + '.out')
    with open(outp, 'w') as fo:
        subprocess.run(cmd, stdout=fo, stderr=subprocess.DEVNULL)
    out = open(outp).read()
    dt = time.time() - t0
    if 's UNSATISFIABLE' in out:
        print('UNSAT', tag, 'vars', nv[0], 'clauses', ncls, '%.1fs' % dt); return
    if 's SATISFIABLE' not in out:
        print('UNKNOWN', tag, '%.1fs' % dt); return
    true = set()
    for line in out.splitlines():
        if line.startswith('v '):
            for t in line[2:].split():
                t = int(t)
                if t > 0: true.add(t)
    gates = []
    for j in range(S):
        sel = [o for o in opts[j] if o[0] in true]
        assert len(sel) == 1
        _, k, a, b = sel[0]; gates.append((k, a, b))
    # verify by simulation
    ok = True
    for r in rows:
        w = [(r >> i) & 1 for i in range(n)]
        for k, a, b in gates:
            w.append((w[a] & w[b]) if k == 'and' else (w[a] | w[b]) if k == 'or' else 1 - w[a])
        if w[-1] != tt[r]: ok = False; break
    print('SAT' if ok else 'SAT-BUT-REPLAY-FAILED', tag, '%.1fs' % dt)
    for k, a, b in gates:
        print({'and': 0, 'or': 1, 'not': 2}[k], a, b)

main()
