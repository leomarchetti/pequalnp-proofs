"""Generate a size-split reduction and its small-size child proof for an iff-characterised gap.

usage: gen_size.py gaps.json GAP_NUMBER K t [outdir]
  t: the small side is `x1.size ≤ t` (choose t = (number of essential inputs) - 2).
Writes outdir/R_meta_<N>_<K>.lean (reduction) and outdir/child_size_<N>.lean (small side, uses DepKit)
and outdir/h_small_<N>.txt (the small-side statement, for the auto-submitter).
The child proof finds the circuit-class hypothesis, the size bound and the characterisation by
`assumption`, so the hypothesis order of the statement does not matter.
"""
import json, re, sys, os

gaps, num, K, t = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
out = sys.argv[5] if len(sys.argv) > 5 else '.pnp/size'
G = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}
s = G['L-meta-' + num]['statement'].strip()
cls = re.search(r'(PEqualNP\.MetaComplexity\.(Monotone2|FanInTwo) x1|PEqualNP\.TopForm\.IsAO2 \((\d+) : ℕ\) x1) →', s)
anchor = cls.group(0)
assert s.count(anchor) == 1
# the characterisation hypothesis: (∀ (xK : Fin (n : ℕ) → Bool), x1.eval (List.ofFn xK) = Bool.true ↔ RHS)
m = re.search(r'\(∀ \((x\d+) : Fin \((\d+) : ℕ\) → Bool\), x1\.eval \(List\.ofFn \1\) = Bool\.true ↔ ', s)
var, n = m.group(1), int(m.group(2))
i0 = m.start(); depth = 0; k = i0
while True:
    c = s[k]; depth += (c == '(') - (c == ')'); k += 1
    if depth == 0: break
hyp = s[i0 + 1:k - 1]                      # without the outer parentheses
rhs = hyp[hyp.index('↔ ') + 2:]
SMALL = f'x1.size ≤ ({t} : ℕ)'
h_small = s.replace(anchor, anchor + ' ' + SMALL + ' →')
h_big = s.replace(anchor, anchor + ' (' + str(t) + ' : ℕ) < x1.size →')
os.makedirs(out, exist_ok=True)
open(os.path.join(out, f'R_meta_{num}_{K}.lean'), 'w', encoding='utf-8', newline='\n').write(f"""import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_{num}_{K}
    (h1 : {h_small})
    (h2 : {h_big}) :
    {s} := by
  intro x1
  by_cases h : {SMALL}
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> first | assumption | omega
""")
open(os.path.join(out, f'h_small_{num}.txt'), 'w', encoding='utf-8', newline='\n').write(h_small)
kit = open(os.path.join(out, 'depkit.lean'), encoding='utf-8').read()
kit = kit[kit.index('namespace PEqualNP.Outside.DepKit'):kit.index('end PEqualNP.Outside.DepKit') + len('end PEqualNP.Outside.DepKit')]
R = f'(fun {var} : Fin {n} → Bool => {rhs})'
fan = ('(fun g hg => le_of_eq ((‹PEqualNP.TopForm.IsAO2 _ C›).2.2 g hg))' if 'IsAO2' in anchor
       else '(fun g hg => (‹PEqualNP.MetaComplexity.Monotone2 C› g hg).2)')
child = f"""import PEqualNP.Defs

{kit}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem child_size_{num} : {h_small} := by
  intro C
  intros
  exfalso
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := {fan}
  have hsmall : C.size ≤ {t} := by assumption
  have hiff : ∀ {var} : Fin {n} → Bool, C.eval (List.ofFn {var}) = Bool.true ↔ {rhs.replace('x1', 'C')} := by assumption
  have key : ∀ i : Fin {n}, i.val ∈ (Finset.univ.filter fun i : Fin {n} => ∃ j : Fin {n}, i ≠ j ∧
      ¬ {R} (fun k => decide (k = j)) ∧ {R} (fun k => decide (k = j ∨ k = i))).map Fin.valEmbedding →
      ∃ j : Fin {n}, i ≠ j ∧ ¬ {R} (fun k => decide (k = j)) ∧ {R} (fun k => decide (k = j ∨ k = i)) := by
    intro i hi
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply] at hi
    obtain ⟨i', hi', he⟩ := hi
    rw [Fin.ext (he)] at hi'
    exact hi'
  have hb := PEqualNP.Outside.DepKit.boundE {n} C hfan
    ((Finset.univ.filter fun i : Fin {n} => ∃ j : Fin {n}, i ≠ j ∧
      ¬ {R} (fun k => decide (k = j)) ∧ {R} (fun k => decide (k = j ∨ k = i))).map Fin.valEmbedding)
    (by intro i hi; simp only [Finset.mem_map, Fin.valEmbedding_apply] at hi; obtain ⟨a, _, rfl⟩ := hi; exact a.isLt)
    (by
      intro i hi
      have hin : i < {n} := by
        simp only [Finset.mem_map, Fin.valEmbedding_apply] at hi; obtain ⟨a, _, rfl⟩ := hi; exact a.isLt
      obtain ⟨j, hij, h0, h1⟩ := key ⟨i, hin⟩ hi
      exact PEqualNP.Outside.DepKit.ess_of_pair C {R} hiff ⟨i, hin⟩ j hij h0 h1)
  have hcard : ((Finset.univ.filter fun i : Fin {n} => ∃ j : Fin {n}, i ≠ j ∧
      ¬ {R} (fun k => decide (k = j)) ∧ {R} (fun k => decide (k = j ∨ k = i))).map Fin.valEmbedding).card = {t + 2} := by
    decide +kernel
  omega
"""
open(os.path.join(out, f'child_size_{num}.lean'), 'w', encoding='utf-8', newline='\n').write(child)
print('written', num, 'n=', n, 't=', t, 'var', var)
