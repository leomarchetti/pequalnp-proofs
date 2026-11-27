"""Answer bank for small circuit FIND steps: proven intervals and circuits per symmetry class, plus lookup.

Kinds:
  rep  : n x m bipartite graph on the one-a-side promise. Wires 0..n-1 rows, n..n+m-1 columns; bit m*u+v = edge (u,v).
         Classes up to row permutations and column permutations (and transposition when n == m).
  pair : graph on n vertices, inputs with one or two vertices on (pair functions). Wires 0..n-1; bit n*i+j for i <= j
         (the steps' encoding: n * min + max). Classes up to vertex permutations.
Modes: 'g' AND/OR/NOT (FanInTwo), 'm' AND/OR only (Monotone2).
A circuit is a list of [op, a, b] (op 0 AND, 1 OR, 2 NOT reading a), output = last gate (as the solver writes them).

Bank file bank_<kind>_<n>x<m>.json: {canonical mask (str): {"g": [lb, ub, circuit or null], "m": [...]}}.
Every answer handed out is relabeled to the step's own wires and checked on every promise input before it is returned.
"""
import itertools, json, os

DIR = os.path.dirname(os.path.abspath(__file__))

# ---------- canonical forms with the mapping back ----------
def rep_canon(mask, n, m):
    """-> (canonical mask, t, p, q): C = transform(mask); with t False, C[p[u]][q[v]] = mask[u][v];
    with t True (n == m), C[q[v]][p[u]] = mask[u][v]"""
    best = None
    for t in ((False, True) if n == m else (False,)):
        R, Cn = (n, m) if not t else (m, n)
        get = (lambda u, v: (mask >> (m * u + v)) & 1) if not t else (lambda u, v: (mask >> (m * v + u)) & 1)
        # in the transposed view, "row" a is the original column a and "column" b the original row b
        for q in itertools.permutations(range(Cn)):
            rows = []
            for a in range(R):
                r = 0
                for b in range(Cn):
                    if get(a, b): r |= 1 << q[b]
                rows.append((r, a))
            rows.sort()
            c = sum(r << (Cn * i) for i, (r, a) in enumerate(rows))
            if best is None or c < best[0]:
                p = [0] * R
                for i, (r, a) in enumerate(rows): p[a] = i
                best = (c, t, tuple(p), tuple(q))
    return best

def pair_canon(mask, n):
    """-> (canonical mask, p): canonical bit (n*min(p_i,p_j) + max) = mask bit (n*min(i,j) + max(i,j))"""
    best = None
    edges = [(i, j) for i in range(n) for j in range(i, n) if (mask >> (n * i + j)) & 1]
    for p in itertools.permutations(range(n)):
        c = 0
        for i, j in edges:
            a, b = sorted((p[i], p[j])); c |= 1 << (n * a + b)
        if best is None or c < best[0]: best = (c, tuple(p))
    return best

# ---------- evaluation and relabeling ----------
def evaluate(gates, inputs):
    w = list(inputs)
    for op, a, b in gates:
        w.append((w[a] and w[b]) if op == 0 else (w[a] or w[b]) if op == 1 else (not w[a]))
    return w[-1] if gates else False

def rep_ok(gates, mask, n, m, allow_not):
    if not allow_not and any(op == 2 for op, a, b in gates): return False
    for u in range(n):
        for v in range(m):
            x = [i == u for i in range(n)] + [j == v for j in range(m)]
            if evaluate(gates, x) != bool((mask >> (m * u + v)) & 1): return False
    return True

def pair_ok(gates, mask, n, allow_not):
    if not allow_not and any(op == 2 for op, a, b in gates): return False
    for i in range(n):
        for j in range(i, n):
            x = [k in (i, j) for k in range(n)]
            if evaluate(gates, x) != bool((mask >> (n * i + j)) & 1): return False
    return True

def relabel(gates, wire_map, n_inputs):
    """replace input wires (< n_inputs) through wire_map; gate wires keep their numbers"""
    f = lambda w: wire_map[w] if w < n_inputs else w
    return [[op, f(a), f(b) if op != 2 else b] for op, a, b in gates]

def rep_map(t, p, q, n, m):
    """wire map from the canonical circuit's inputs to the step's inputs"""
    pinv = {v: k for k, v in enumerate(p)}; qinv = {v: k for k, v in enumerate(q)}
    wm = {}
    if not t:   # canonical row p[u] = step row u, canonical column q[v] = step column v
        for i in range(n): wm[i] = pinv[i]
        for j in range(m): wm[n + j] = n + qinv[j]
    else:       # canonical row a = step column (p^-1(a)), canonical column b = step row (q^-1(b)); n == m
        for i in range(n): wm[i] = n + pinv[i]
        for j in range(m): wm[n + j] = qinv[j]
    return wm

# ---------- bank storage ----------
def path(kind, n, m): return os.path.join(DIR, 'bank_%s_%dx%d.json' % (kind, n, m))
_cache = {}
def load(kind, n, m):
    """the bank for this kind and size, reloaded whenever its file changes (banks are written while the racer runs)"""
    p = path(kind, n, m)
    try: mt = os.path.getmtime(p)
    except OSError: return None
    key = (kind, n, m)
    if key not in _cache or _cache[key][0] != mt:
        try: _cache[key] = (mt, json.load(open(p)))
        except (OSError, ValueError): return _cache.get(key, (None, None))[1]
    return _cache[key][1]

def lookup(kind, mask, n, m, mode, bound):
    """-> ('circuit', gates) with at most `bound` gates on the step's own wires (verified), ('impossible', lb) when
    the bank proves no circuit of at most `bound` gates exists, or (None, None) when the bank does not know."""
    B = load(kind, n, m)
    if not B: return None, None
    if kind == 'rep':
        c, t, p, q = rep_canon(mask, n, m)
        e = B.get(str(c))
        if not e: return None, None
        lb, ub, circ = e[mode]
        if lb is not None and lb > bound: return 'impossible', lb
        if circ is not None and len(circ) <= bound:
            g = relabel(circ, rep_map(t, p, q, n, m), n + m)
            if rep_ok(g, mask, n, m, mode == 'g'): return 'circuit', g
    else:
        c, p = pair_canon(mask, n)
        e = B.get(str(c))
        if not e: return None, None
        lb, ub, circ = e[mode]
        if lb is not None and lb > bound: return 'impossible', lb
        if circ is not None and len(circ) <= bound:
            pinv = {v: k for k, v in enumerate(p)}
            g = relabel(circ, {i: pinv[i] for i in range(n)}, n)
            if pair_ok(g, mask, n, mode == 'g'): return 'circuit', g
    return None, None

# ---------- the row/column construction (upper bounds without the solver), as a circuit ----------
def rep_construction(mask, n, m):
    """the better of: group rows by their column sets (OR of the group's rows AND OR of the set's columns, then OR
    over the groups) or the same with columns; returns a gate list with output = last gate, or None for size 0"""
    full = (1 << (n * m)) - 1
    if mask == 0: return None
    if mask == full: return [[0, 0, 0]] if False else None   # constants are not in the solver's gate model
    best = None
    for side in ('row', 'col'):
        if side == 'row':
            sets = [(mask >> (m * u)) & ((1 << m) - 1) for u in range(n)]; own, other, no, offo = n, m, 0, n
        else:
            sets = [sum(((mask >> (m * u + v)) & 1) << u for u in range(n)) for v in range(m)]; own, other, no, offo = m, n, n, 0
        groups = {}
        for i, s in enumerate(sets):
            if s: groups.setdefault(s, []).append(i)
        gates = []; w = [n + m]
        def OR(ws):
            cur = ws[0]
            for x in ws[1:]:
                gates.append([1, cur, x]); cur = n + m + len(gates) - 1
            return cur
        terms = []
        for s, members in groups.items():
            a = OR([no + i for i in members])
            others = [offo + j for j in range(other) if (s >> j) & 1]
            if len(others) == other: terms.append(a); continue
            b = OR(others)
            gates.append([0, a, b]); terms.append(n + m + len(gates) - 1)
        out = OR(terms)
        if out < n + m:   # the answer is an input wire: one OR with itself keeps the solver's "output = last gate" form
            gates.append([1, out, out])
        elif gates and out != n + m + len(gates) - 1:
            gates.append([1, out, out])
        if rep_ok(gates, mask, n, m, False) and (best is None or len(gates) < len(best)): best = gates
    return best
