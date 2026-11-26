import PEqualNP.Defs

namespace PEqualNP.Outside.Kit
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


lemma splitEval {n : ℕ} (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x y : Fin n → Bool) : C.eval (List.ofFn (fun i => x i || y i)) =
    (C.eval (List.ofFn x) || C.eval (List.ofFn y)) := by
  unfold Circuit.eval Circuit.wires
  refine wire_split C.gates ho _ _ _ (by simp) (by simp) ?_ C.output
  intro i
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

/-- Monotonicity of an OR-only circuit on `Fin n` inputs. -/
lemma mono {n : ℕ} (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (x z : Fin n → Bool)
    (hle : ∀ i, x i = true → z i = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn z) = true := by
  have e := splitEval C ho x z
  have hz : (fun i => x i || z i) = z := by
    funext i; cases hxi : x i <;> cases hzi : z i <;> simp_all
  rw [hz, hx, Bool.true_or] at e
  exact e


end PEqualNP.Outside.Kit

set_option maxRecDepth 20000 in
theorem child_18207 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 = PEqualNP.ReadTwo.fpl (13 : ℕ) fun (x5 x6 : Fin (13 : ℕ)) => ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →           have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = x7)) x6 x7;           x6 (0 : ℕ) (13 : ℕ) = Bool.false →             x6 (13 : ℕ) (0 : ℕ) = Bool.false →               have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);               have x10 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x10 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x10 - (26 : ℕ));               have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>                 have x13 : PEqualNP.CircuitLowerBounds.Gate := x10 x12;                 have x14 : ℕ := x13.inputs.getD (0 : ℕ) (0 : ℕ);                 (26 : ℕ) ≤ x12 ∧ x11 ∈ x13.inputs ∧ (x13.op.eval [Bool.false, Bool.true] = Bool.false ∨ x11 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x13.inputs.getD (1 : ℕ) (0 : ℕ));               have x12 : ℕ → ℕ → ℕ → Prop := fun (x12 x13 x14 : ℕ) =>                 have x15 : Set ℕ := {x15 : ℕ | x9 {x12} x15 = Bool.true ∧ x9 {x13} x15 = Bool.false};                 have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x16 ∈ (x10 x17).inputs ∧ x16 ∈ x15 ∧ x17 ∈ x15;                 PEqualNP.ReadTwo.isAnd x1 x14 ∧ Relation.ReflTransGen x11 ((26 : ℕ) + x14) x1.output ∧ ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, x17 ∈ x15 ∧ Relation.ReflTransGen x16 x12 x17;               (∃ (x13 : ℕ), x12 (0 : ℕ) (13 : ℕ) x13) → (∃ (x14 : ℕ), x12 (13 : ℕ) (0 : ℕ) x14) → (65 : ℕ) ≤ x1.size := by
  intro C _ hAO hNo _ hfun
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    rcases hAO.1 g hg with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  let x : Fin 26 → Bool := fun i => decide (i = 0)
  let y : Fin 26 → Bool := fun i => decide (i = 13)
  have hx : C.eval (List.ofFn x) = false := by
    have h := congrFun hfun x
    simp only [PEqualNP.MetaComplexity.circuitFun] at h
    rw [h]; decide +kernel
  have hy : C.eval (List.ofFn y) = false := by
    have h := congrFun hfun y
    simp only [PEqualNP.MetaComplexity.circuitFun] at h
    rw [h]; decide +kernel
  have hp : C.eval (List.ofFn (fun i => x i || y i)) = true := by
    have h := congrFun hfun (fun i => x i || y i)
    simp only [PEqualNP.MetaComplexity.circuitFun] at h
    rw [h]; decide +kernel
  rw [PEqualNP.Outside.Kit.splitEval C onlyOr x y, hx, hy] at hp
  exact Bool.false_ne_true hp
