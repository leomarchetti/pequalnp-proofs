import PEqualNP.Defs

namespace PEqualNP.Outside.ChildInc
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

end PEqualNP.Outside.ChildInc

set_option maxRecDepth 20000 in
theorem child_17361 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) →     x1.size < (64 : ℕ) →       ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (1 : ℕ) →         ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (1 : ℕ) →           (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) →             (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x1.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x7 x8 = Bool.true) →               ∃ (x8 : Bool) (x9 : Fin (13 : ℕ)) (x10 : (x10 : Fin (5 : ℕ)) → Fin (x1.size - ↑x10)) (x11 : Fin (5 : ℕ) → ℕ),                 have x12 : PEqualNP.CircuitLowerBounds.Circuit := List.foldl (fun (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : Fin (5 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x12 (↑(x10 x13)) (x11 x13)) x1 (List.finRange (5 : ℕ));                 ∀ (x13 x14 : Finset (Fin (13 : ℕ))), (if x8 = Bool.true then x9 ∉ x13 else x9 ∉ x14) → x12.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = x1.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) := by
  intro C hM hNo _ _ _ hacc hsound
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  have hz := hacc 0 0 (by decide)
  have hs := PEqualNP.Outside.ChildInc.evalOr C onlyOr
    (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)))
    (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({0} : Finset (Fin 13)))
    (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13)))
    (by simp [PEqualNP.GenericRejection.incidenceInput])
    (by simp [PEqualNP.GenericRejection.incidenceInput]) (by
      intro i
      rcases Nat.lt_or_ge i 26 with h | h
      · interval_cases i <;> decide
      · rw [List.getD_eq_default, List.getD_eq_default, List.getD_eq_default] <;>
          simp [PEqualNP.GenericRejection.incidenceInput] <;> omega)
  rw [hz] at hs
  cases hx : C.eval (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)))
  · rw [hx, Bool.false_or] at hs
    have := hsound ∅ {0} hs.symm
    revert this; decide
  · have := hsound {0} ∅ hx
    revert this; decide
