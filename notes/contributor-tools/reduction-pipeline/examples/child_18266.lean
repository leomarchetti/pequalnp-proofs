import PEqualNP.Defs

namespace PEqualNP.Outside.ChildMono
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

/-- Monotonicity of an OR-only circuit on `Fin n` inputs. -/
lemma mono {n : ℕ} (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (x z : Fin n → Bool)
    (hle : ∀ i, x i = true → z i = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn z) = true := by
  have e := splitEval C ho x z
  have hz : (fun i => x i || z i) = z := by
    funext i; cases hxi : x i <;> cases hzi : z i <;> simp_all
  rw [hz, hx, Bool.true_or] at e
  exact e

end PEqualNP.Outside.ChildMono

theorem child_18266 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) →     x1.size ≤ (18 : ℕ) →       have x4 : ℕ → Bool := fun (x4 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x4.testBit ↑x5;       (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x4 x5 = Bool.true) → ∃ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x4 x6 = Bool.true := by
  intro C hAO hNo _ x4 hall
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    rcases hAO.1 g hg with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  have h3 : C.eval (List.ofFn fun i : Fin 10 => (3 : ℕ).testBit i) = true := hall 3 (by simp)
  have hsplit := PEqualNP.Outside.ChildMono.splitEval C onlyOr
    (fun i : Fin 10 => (1 : ℕ).testBit i) (fun i : Fin 10 => (2 : ℕ).testBit i)
  have h12 : (fun i : Fin 10 => (1 : ℕ).testBit i || (2 : ℕ).testBit i) = fun i : Fin 10 => (3 : ℕ).testBit i := by
    funext i; revert i; decide
  rw [h12, h3] at hsplit
  cases h1 : C.eval (List.ofFn fun i : Fin 10 => (1 : ℕ).testBit i)
  · rw [h1, Bool.false_or] at hsplit
    exact ⟨50, by simp, PEqualNP.Outside.ChildMono.mono C onlyOr _ _ (by decide) hsplit.symm⟩
  · exact ⟨69, by simp, PEqualNP.Outside.ChildMono.mono C onlyOr _ _ (by decide) h1⟩
