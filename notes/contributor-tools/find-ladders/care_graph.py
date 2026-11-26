"""Care rows for monotone synthesis of a monotone graph property on K_n edge bits.
A monotone circuit equals f iff it is true on every minterm and false on every maximal false point.
usage: care_graph.py PROP n out.txt      PROP in: conn, k4, pm, tri
Edge order is lexicographic: (0,1),(0,2),...,(n-2,n-1)  (matches the desk statements checked so far).
Also prints the full truth table as hex (bit r = f(row r), input i = bit i of r).
"""
import sys, itertools
prop, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
E = list(itertools.combinations(range(n), 2))
m = len(E)

def adj(r):
    A = [set() for _ in range(n)]
    for k, (a, b) in enumerate(E):
        if r >> k & 1: A[a].add(b); A[b].add(a)
    return A

def conn(r):
    A = adj(r); seen = {0}; st = [0]
    while st:
        u = st.pop()
        for w in A[u]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n

def clique(r, k):
    A = adj(r)
    return any(all(b in A[a] for a, b in itertools.combinations(S, 2)) for S in itertools.combinations(range(n), k))

def pm(r):
    A = adj(r)
    def go(left):
        if not left: return True
        a = left[0]
        return any(b in A[a] and go([x for x in left[1:] if x != b]) for b in left[1:])
    return go(list(range(n)))

f = {'conn': conn, 'k4': lambda r: clique(r, 4), 'pm': pm, 'tri': lambda r: clique(r, 3)}[prop]
tt = [f(r) for r in range(1 << m)]
for r in range(1 << m):          # sanity: monotone
    if tt[r]:
        for i in range(m):
            assert tt[r | (1 << i)]
mins = [r for r in range(1 << m) if tt[r] and all(not tt[r & ~(1 << i)] for i in range(m) if r >> i & 1)]
maxf = [r for r in range(1 << m) if not tt[r] and all(tt[r | (1 << i)] for i in range(m) if not r >> i & 1)]
with open(out, 'w') as fo:
    for r in mins: fo.write(f'{r} 1\n')
    for r in maxf: fo.write(f'{r} 0\n')
print(prop, n, 'inputs', m, 'minterms', len(mins), 'maximal false', len(maxf))
if m <= 10:
    print('hex', hex(sum(1 << r for r in range(1 << m) if tt[r]))[2:])
