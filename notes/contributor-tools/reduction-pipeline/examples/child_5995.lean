import PEqualNP.Defs

namespace PEqualNP.Outside.Child5995
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

lemma splitEval {n : ℕ} (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x y : Fin n → Bool) : C.eval (List.ofFn (fun i => x i || y i)) =
    (C.eval (List.ofFn x) || C.eval (List.ofFn y)) := by
  unfold Circuit.eval Circuit.wires
  refine wire_split C.gates ho _ _ _ (by simp) (by simp) ?_ C.output
  intro i
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

end PEqualNP.Outside.Child5995

theorem child_5995 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → x1.size ≤ (63 : ℕ) → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → ∃ (x5 : Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x8 ≠ x5 ∧ Fin.natAdd (13 : ℕ) x9 ≠ x5 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true := by
  intro C hAO hNo _ evaluates
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    rcases hAO.1 g hg with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  let x : Fin 26 → Bool := fun i => decide (i = 0)
  let y : Fin 26 → Bool := fun i => decide (i = 13)
  have hx : ¬ C.eval (List.ofFn x) = true := by
    intro h
    have no := (evaluates x).mp h
    revert no
    decide +kernel
  have hy : ¬ C.eval (List.ofFn y) = true := by
    intro h
    have no := (evaluates y).mp h
    revert no
    decide +kernel
  have hp := (evaluates (fun i => x i || y i)).mpr ⟨0, 0, by decide +kernel⟩
  rw [PEqualNP.Outside.Child5995.splitEval C onlyOr x y, Bool.or_eq_true] at hp
  exact hp.elim hx hy
