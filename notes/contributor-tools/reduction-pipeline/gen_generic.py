"""Generic child prover: emit candidate proofs for a posted statement from five templates.

usage: gen_generic.py <statement file> <outdir> <tag>
Writes outdir/<tag>_<T>.lean for each applicable template; each file is `import PEqualNP.Defs`, the
GenKit namespace, then `theorem child_<tag> : <statement> := by ...`. Prints the files written.
The statement must quantify a circuit `x1` first (optionally wrapped in parentheses) and carry
Monotone2 or IsAO2 for it. Hypotheses are found by `assumption`, so their order does not matter,
and every witness is found by `decide`, so no per-gap data is needed.
  with an iff hypothesis  ∀ (x : Fin n → Bool), x1.eval (List.ofFn x) = Bool.true ↔ R x :
    T1   no AND gate        -> OR-only split on an edge
    T2_t x1.size ≤ t        -> connectivity bound with the essential inputs
    T3   x1.output < n      -> the output is an input bit; every singleton is rejected
  with a conclusion       ∃ (x : Fin n → Bool), x1.eval (List.ofFn x) ≠ F :
    T1b  no AND gate        -> OR-only split on an edge of F
    T3b  x1.output < n      -> the singleton on the output wire
"""
import re, sys, os

stmt_orig = open(sys.argv[1], encoding='utf-8').read().strip()
out, tag = sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)
kitsrc = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'genkit.lean'), encoding='utf-8').read()
kit = kitsrc[kitsrc.index('namespace PEqualNP.Outside.GenKit'):]
NS = 'PEqualNP.Outside.GenKit'

def wrapped(t):
    if not (t.startswith('(') and t.endswith(')')): return False
    d = 0
    for i, c in enumerate(t):
        d += (c == '(') - (c == ')')
        if d == 0 and i < len(t) - 1: return False
    return True

stmt = stmt_orig
while wrapped(stmt): stmt = stmt[1:-1].strip()
if not stmt.startswith('∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit)'):
    sys.exit(0)
cls = re.search(r'(PEqualNP\.MetaComplexity\.Monotone2 x1|PEqualNP\.TopForm\.IsAO2 \((\d+) : ℕ\) x1)', stmt)
if not cls:
    sys.exit(0)
mono = 'Monotone2' in cls.group(0)
m = re.search(r'\(∀ \((x\d+) : Fin \((\d+) : ℕ\) → Bool\), x1\.eval \(List\.ofFn \1\) = Bool\.true ↔ ', stmt)
cm = re.search(r'∃ \((x\d+) : Fin \((\d+) : ℕ\) → Bool\), x1\.eval \(List\.ofFn \1\) ≠ (.+)$', stmt)
noand = re.search(r'¬\s*\(?\s*∃ \((x\d+|j) : Fin x1\.gates\.length\), \(x1\.gates\.get \1\)\.op = PEqualNP\.CircuitLowerBounds\.GateOp\.and', stmt)

if mono:
    OPS = """    have hop := (‹PEqualNP.MetaComplexity.Monotone2 C› g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hA | hO"""
    FAN = '(fun g hg => (‹PEqualNP.MetaComplexity.Monotone2 C› g hg).2)'
else:
    OPS = "    rcases (‹PEqualNP.TopForm.IsAO2 _ C›).1 g hg with hA | hO"
    FAN = '(fun g hg => le_of_eq ((‹PEqualNP.TopForm.IsAO2 _ C›).2.2 g hg))'
ONLYOR = f"""  have hNo : ¬∃ x : Fin C.gates.length, (C.gates.get x).op = PEqualNP.CircuitLowerBounds.GateOp.and := by assumption
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
{OPS}
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hA⟩).elim
    · exact hO
"""
def EVALOUT(n):
    return f"""  have hval : C.eval (List.ofFn (fun k : Fin {n} => decide (k = (⟨C.output, hout⟩ : Fin {n})))) = true := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [{NS}.wires_prefix _ _ _ (by simp; exact hout)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hout]
"""

cands = {}
if m:
    var, n = m.group(1), int(m.group(2))
    i0 = m.start(); depth = 0; k = i0
    while True:
        c = stmt[k]; depth += (c == '(') - (c == ')'); k += 1
        if depth == 0: break
    rhs = stmt[i0 + 1:k - 1]
    rhs = rhs[rhs.index('↔ ') + 2:]
    rhsC = re.sub(r'\bx1\b', 'C', rhs)
    R = f'(fun {var} : Fin {n} → Bool => {rhsC})'
    def e(i): return f'(fun k : Fin {n} => decide (k = {i}))'
    HEAD = f"""  intro C
  intros
  exfalso
  have hiff : ∀ {var} : Fin {n} → Bool, C.eval (List.ofFn {var}) = Bool.true ↔ {rhsC} := by assumption
"""
    if noand:
        cands['T1'] = HEAD + ONLYOR + f"""  have key : ∃ i j : Fin {n}, ¬ {R} {e('i')} ∧ ¬ {R} {e('j')} ∧
      {R} (fun k : Fin {n} => decide (k = i) || decide (k = j)) := by decide +kernel
  obtain ⟨i, j, hi, hj, hij⟩ := key
  have a := (hiff (fun k : Fin {n} => decide (k = i) || decide (k = j))).mpr hij
  rw [{NS}.splitEval C onlyOr {e('i')} {e('j')}] at a
  have hx : C.eval (List.ofFn {e('i')}) ≠ true := fun h => hi ((hiff _).mp h)
  have hy : C.eval (List.ofFn {e('j')}) ≠ true := fun h => hj ((hiff _).mp h)
  cases hcx : C.eval (List.ofFn {e('i')}) <;> cases hcy : C.eval (List.ofFn {e('j')}) <;> simp_all
"""
    for t in sorted({int(x) for x in re.findall(r'x1\.size ≤ \((\d+) : ℕ\) →', stmt)}):
        if t + 2 > n: continue
        ESS = f"""((Finset.univ.filter fun i : Fin {n} => ∃ j : Fin {n}, i ≠ j ∧
      ¬ {R} (fun k => decide (k = j)) ∧ {R} (fun k => decide (k = j ∨ k = i))).map Fin.valEmbedding)"""
        cands[f'T2_{t}'] = HEAD + f"""  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := {FAN}
  have hsmall : C.size ≤ {t} := by assumption
  have hb := {NS}.boundE {n} C hfan {ESS}
    (by intro i hi; simp only [Finset.mem_map, Fin.valEmbedding_apply] at hi; obtain ⟨a, _, rfl⟩ := hi; exact a.isLt)
    (by
      intro i hi
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply] at hi
      obtain ⟨a, ⟨j, hij, h0, h1⟩, rfl⟩ := hi
      exact {NS}.ess_of_pair C {R} hiff a j hij h0 h1)
  have hcard : {t + 2} ≤ {ESS}.card := by decide +kernel
  omega
"""
    if re.search(rf'x1\.output < \({n} : ℕ\) →', stmt):
        cands['T3'] = HEAD + f"""  have hout : C.output < {n} := by assumption
  have key : ∀ v : Fin {n}, ¬ {R} (fun k : Fin {n} => decide (k = v)) := by decide +kernel
""" + EVALOUT(n) + """  exact key ⟨C.output, hout⟩ ((hiff _).mp hval)
"""
elif cm:
    cvar, n, F = cm.group(1), int(cm.group(2)), cm.group(3).strip()
    FB = f'(fun {cvar} : Fin {n} → Bool => {F})'
    def e(i): return f'(fun k : Fin {n} => decide (k = {i}))'
    HEADC = """  intro C
  intros
"""
    if noand:
        cands['T1b'] = HEADC + ONLYOR + f"""  have key : ∃ i j : Fin {n}, {FB} {e('i')} = false ∧ {FB} {e('j')} = false ∧
      {FB} (fun k : Fin {n} => decide (k = i) || decide (k = j)) = true := by decide +kernel
  obtain ⟨i, j, hi, hj, hij⟩ := key
  by_cases a : C.eval (List.ofFn {e('i')}) = true
  · exact ⟨{e('i')}, fun h => by rw [a] at h; exact absurd (h.trans hi) (by decide)⟩
  by_cases b : C.eval (List.ofFn {e('j')}) = true
  · exact ⟨{e('j')}, fun h => by rw [b] at h; exact absurd (h.trans hj) (by decide)⟩
  refine ⟨(fun k : Fin {n} => decide (k = i) || decide (k = j)), fun h => ?_⟩
  rw [{NS}.splitEval C onlyOr {e('i')} {e('j')}] at h
  simp only [Bool.not_eq_true] at a b
  rw [a, b] at h
  exact absurd (h.trans hij) (by decide)
"""
    if re.search(rf'x1\.output < \({n} : ℕ\) →', stmt):
        cands['T3b'] = HEADC + f"""  have hout : C.output < {n} := by assumption
  have key : ∀ v : Fin {n}, {FB} (fun k : Fin {n} => decide (k = v)) = false := by decide +kernel
""" + EVALOUT(n) + f"""  refine ⟨(fun k : Fin {n} => decide (k = (⟨C.output, hout⟩ : Fin {n}))), fun h => ?_⟩
  have kk := key ⟨C.output, hout⟩
  rw [hval] at h
  exact absurd (h.trans kk) (by decide)
"""

written = []
for name, body in cands.items():
    fn = os.path.join(out, f'{tag}_{name}.lean')
    open(fn, 'w', encoding='utf-8', newline='\n').write(
        'import PEqualNP.Defs\n\n' + kit + '\n\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 4000000 in\n'
        + f'theorem child_{tag} : {stmt_orig} := by\n' + body)
    written.append(fn)
print(' '.join(written))
