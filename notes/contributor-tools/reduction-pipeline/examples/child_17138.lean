import PEqualNP.Defs

namespace PEqualNP.Outside.Child17138
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma app_read (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = w.length
    · simp [he]
    · rw [if_neg he]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma wire_split (gs : List Gate) (ho : ∀ g ∈ gs, g.op = GateOp.or)
    (x y z : List Bool) (hy : y.length = x.length) (hz : z.length = x.length)
    (h : ∀ i, z.getD i false = (x.getD i false || y.getD i false)) :
    ∀ i, (gs.foldl step z).getD i false =
      ((gs.foldl step x).getD i false || (gs.foldl step y).getD i false) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
      simp only [List.foldl_cons]
      refine ih (fun q hq => ho q (List.mem_cons_of_mem _ hq)) _ _ _ ?_ ?_ ?_
      · simp [step, hy]
      · simp [step, hz]
      · intro i
        have hg : g.op = GateOp.or := ho g (by simp)
        simp only [step, app_read, hy, hz]
        split
        · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, id_eq, h]
          generalize g.inputs = inputs
          induction inputs with
          | nil => rfl
          | cons a rest ih =>
              simp only [List.any_cons, ih]
              ac_rfl
        · exact h i

/-- On an OR-only circuit, evaluation of a pointwise OR of two equal-length inputs splits. -/
lemma evalOr (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (x y z : List Bool)
    (hy : y.length = x.length) (hz : z.length = x.length)
    (h : ∀ i, z.getD i false = (x.getD i false || y.getD i false)) :
    C.eval z = (C.eval x || C.eval y) := by
  unfold Circuit.eval Circuit.wires
  exact wire_split C.gates ho x y z hy hz h C.output

/-- Monotonicity of an OR-only circuit: a larger input of the same length is accepted too. -/
lemma evalMono (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (x z : List Bool)
    (hz : z.length = x.length) (hle : ∀ i, x.getD i false = true → z.getD i false = true)
    (hx : C.eval x = true) : C.eval z = true := by
  have e := evalOr C ho x z z hz hz (by
    intro i; cases hzi : z.getD i false <;> cases hxi : x.getD i false <;> simp_all)
  rw [e, hx]; rfl

/-- Positions at or past the end of a list read the default. -/
lemma getD_past (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

end PEqualNP.Outside.Child17138

set_option maxRecDepth 20000 in
theorem child_17138 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x4 x5 : Fin (13 : ℕ)), x4 - x5 = (0 : Fin (13 : ℕ)) ∨ x4 - x5 = (1 : Fin (13 : ℕ)) ∨ x4 - x5 = (3 : Fin (13 : ℕ)) ∨ x4 - x5 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = x4)) ++ List.ofFn fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 = x5)) = Bool.true) → (∀ (x5 : Finset (Fin (13 : ℕ))), x5.card = (4 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x5 | x8 - x7 = (0 : Fin (13 : ℕ)) ∨ x8 - x7 = (1 : Fin (13 : ℕ)) ∨ x8 - x7 = (3 : Fin (13 : ℕ)) ∨ x8 - x7 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (∀ x9 ∈ x5, ¬(x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hM hNo _ hacc hrej
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  let L : List Bool := (List.ofFn fun i : Fin 13 => decide (i = 0)) ++ List.ofFn fun _ : Fin 13 => false
  let R : List Bool := (List.ofFn fun _ : Fin 13 => false) ++ List.ofFn fun i : Fin 13 => decide (i = 0)
  have hedge := hacc 0 0 (by decide)
  have hsplit := PEqualNP.Outside.Child17138.evalOr C onlyOr L R
    ((List.ofFn fun x7 : Fin 13 => decide (x7 = 0)) ++ List.ofFn fun x7 : Fin 13 => decide (x7 = 0))
    (by simp [L, R]) (by simp [L]) (by
      intro i
      rcases Nat.lt_or_ge i 26 with h | h
      · interval_cases i <;> decide
      · rw [List.getD_eq_default, List.getD_eq_default, List.getD_eq_default] <;> simp [L, R] <;> omega)
  rw [hedge] at hsplit
  have hS1 := hrej {0, 1, 2, 5} (by rfl) (by decide)
  have hS2 := hrej {2, 4, 5, 6} (by rfl) (by decide)
  cases hL : C.eval L
  · rw [hL, Bool.false_or] at hsplit
    exact Bool.false_ne_true (hS2.symm.trans (PEqualNP.Outside.Child17138.evalMono C onlyOr R _
      (by simp [R]) (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> (simp only [R] at hi ⊢; revert hi; decide)
        · rw [List.getD_eq_default _ _ (by simp [R]; omega)] at hi; exact absurd hi (by decide)) hsplit.symm))
  · exact Bool.false_ne_true (hS1.symm.trans (PEqualNP.Outside.Child17138.evalMono C onlyOr L _
      (by simp [L]) (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> (simp only [L] at hi ⊢; revert hi; decide)
        · rw [List.getD_eq_default _ _ (by simp [L]; omega)] at hi; exact absurd hi (by decide)) hL))
