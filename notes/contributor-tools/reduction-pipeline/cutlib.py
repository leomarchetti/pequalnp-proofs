"""Shared helpers for the depth 0-1 cut pipeline (cut_watch.py, send_cut.py).

A desk statement is parsed as: optional `let/have x : T := v;` preludes, then `∀ binders, H1 → ... → C`.
The AND/no-AND cut inserts `A →` / `(¬A) →` right after the circuit's Monotone2/IsAO2 hypothesis.
"""
import re, os, subprocess

ROOT = 'C:/Users/leona/projects/pequalnp-proofs'
ANCHOR = re.compile(r'(PEqualNP\.MetaComplexity\.Monotone2 (x\d+)|PEqualNP\.TopForm\.IsAO2 \((\d+) : ℕ\) (x\d+)) →')

def unwrap(t):
    t = t.strip()
    while t.startswith('(') and t.endswith(')'):
        d = 0
        for i, c in enumerate(t):
            d += (c == '(') - (c == ')')
            if d == 0 and i < len(t) - 1:
                return t
        t = t[1:-1].strip()
    return t

def top_split(s, sep):
    """split s on sep at bracket depth 0"""
    out, d, i, start = [], 0, 0, 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨': d += 1
        elif c in ')]}⟩': d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(s[start:i]); i += len(sep); start = i; continue
        i += 1
    out.append(s[start:])
    return out

def parse(stmt):
    """-> dict(preludes=[names], binders=[names], hyps=[texts], concl=text) or None"""
    s = unwrap(stmt)
    preludes = []
    while s.startswith('let ') or s.startswith('have '):
        name = s.split()[1]
        parts = top_split(s, ';')
        if len(parts) < 2: return None
        preludes.append(name)
        s = ';'.join(parts[1:]).strip()
    if not s.startswith('∀'): return None
    s = s[1:].lstrip()
    binders = []
    i = 0
    while i < len(s) and s[i] in '([{':
        d = 0; j = i
        while True:
            c = s[j]
            if c in '([{': d += 1
            elif c in ')]}': d -= 1
            j += 1
            if d == 0: break
        grp = s[i + 1:j - 1]
        names = grp.split(':')[0].split()
        binders += names
        i = j
        while i < len(s) and s[i] == ' ': i += 1
    if i >= len(s) or s[i] != ',': return None
    body = s[i + 1:].strip()
    parts = [p.strip() for p in top_split(body, ' → ')]
    return dict(preludes=preludes, binders=binders, hyps=parts[:-1], concl=parts[-1])

def andA(var):
    return f'(∃ (x99 : Fin {var}.gates.length), ({var}.gates.get x99).op = PEqualNP.CircuitLowerBounds.GateOp.and)'

def cut(stmt):
    """-> (h1, h2, var, kind, n) or None"""
    ms = list(ANCHOR.finditer(stmt))
    if len(ms) != 1: return None
    m = ms[0]
    var = m.group(2) or m.group(4)
    kind = 'mono' if m.group(2) else 'ao2'
    n = m.group(3)
    before = stmt[:m.start()]
    # the circuit must be bound by a ∀ binder, never by ∃
    if re.search(r'∃ [^,]*\b' + var + r'\b', before): return None
    if not re.search(r'∀ [^,]*\b' + var + r'\b[^,]*: PEqualNP\.CircuitLowerBounds\.Circuit', before): return None
    a = m.group(0)
    A = andA(var)
    return stmt.replace(a, a + ' ' + A + ' →', 1), stmt.replace(a, a + ' (¬' + A + ') →', 1), var, kind, n

def lean_ok(path, timeout=900):
    try:
        r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(path)], cwd=ROOT + '/lean',
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False, 'timeout'
    out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if ': error' in l]
    return r.returncode == 0 and not errs, (errs[0] if errs else '')[:300]

def reduction_file(num, k, stmt, h1, h2, P):
    names = ' '.join(P['preludes'] + P['binders'])
    var = cut(stmt)[2]
    return f"""import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_{num}_{k}
    (h1 : {h1})
    (h2 : {h2}) :
    {stmt} := by
  intro {names}
  by_cases h : {andA(var)}
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> assumption
"""
