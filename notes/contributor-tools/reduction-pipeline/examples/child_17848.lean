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

set_option maxRecDepth 20000 in
theorem child_17848 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) →     have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));     (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hM hNo x3 hq hinc
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  have hQ := hq {0, 1, 2, 5} (by decide +kernel)
  have h1 := hinc (0, 0) (by decide +kernel)
  have h2 := hinc (2, 1) (by decide +kernel)
  simp only [x3] at hQ h1 h2
  have hsplit := PEqualNP.Outside.ChildMono.splitEval C onlyOr
    (fun x4 : Fin (13 + 13) => decide (finSumFinEquiv.symm x4 ∉ ({Sum.inl 0, Sum.inr 0} : Finset (Fin 13 ⊕ Fin 13))))
    (fun x4 : Fin (13 + 13) => decide (finSumFinEquiv.symm x4 ∉ ({Sum.inl 2, Sum.inr 1} : Finset (Fin 13 ⊕ Fin 13))))
  rw [h1, h2] at hsplit
  have hall := PEqualNP.Outside.ChildMono.mono C onlyOr _ (fun _ => true) (fun _ _ => rfl) hQ
  have heq : (fun x4 : Fin (13 + 13) => decide (finSumFinEquiv.symm x4 ∉ ({Sum.inl 0, Sum.inr 0} : Finset (Fin 13 ⊕ Fin 13))) ||
      decide (finSumFinEquiv.symm x4 ∉ ({Sum.inl 2, Sum.inr 1} : Finset (Fin 13 ⊕ Fin 13)))) = fun _ => true := by
    funext x4; revert x4; decide +kernel
  rw [heq] at hsplit
  rw [hsplit] at hall
  simp at hall
