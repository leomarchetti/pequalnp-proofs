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


lemma rejAcc (D : Circuit) (ho : ∀ g ∈ D.gates, g.op = GateOp.or) (a b c R T : List Bool)
    (hcb : c.length = b.length) (hab : a.length = b.length)
    (hsplit : ∀ i, a.getD i false = (b.getD i false || c.getD i false))
    (hRl : R.length = c.length) (hcR : ∀ i, c.getD i false = true → R.getD i false = true)
    (hTl : T.length = b.length) (hbT : ∀ i, b.getD i false = true → T.getD i false = true)
    (ha : D.eval a = true) (hR : D.eval R = false) (hT : D.eval T = false) : False := by
  have e := evalOr D ho b c a hcb hab hsplit
  cases hc : D.eval c
  · rw [ha, hc, Bool.or_false] at e
    have := evalMono D ho b T hTl hbT e.symm
    rw [hT] at this; exact absurd this (by decide)
  · have := evalMono D ho c R hRl hcR hc
    rw [hR] at this; exact absurd this (by decide)

end PEqualNP.Outside.Kit

set_option maxRecDepth 20000 in
theorem child_17824 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x10 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x10 → PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x2 = Bool.false ∨ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x3 = Bool.false) → (50 : ℕ) ≤ Max.max x2 x3 ∧ ∃ x11 ∈ [x2, x3], ∀ (x12 : Fin (26 : ℕ)), ∃ (x13 : Fin (26 : ℕ) → Bool), PEqualNP.LowMerge.wireVal x1 (List.ofFn x13) x11 = Bool.false ∧ PEqualNP.LowMerge.wireVal x1 (List.ofFn (Function.update x13 x12 Bool.true)) x11 = Bool.true := by
  intro C x2 x3 hM hNo _ _ _ hR2 hR3 hq
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  have P01 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 D →
      D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 5} : Finset (Fin 13))) : Finset (Fin 13))) = false → D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 6} : Finset (Fin 13))) : Finset (Fin 13))) = false → False := by
    intro D ho hR hX hY
    exact PEqualNP.Outside.Kit.rejAcc D ho (PEqualNP.GenericRejection.incidenceInput ({6} : Finset (Fin 13)) ({3} : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput ({6} : Finset (Fin 13)) (∅ : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({3} : Finset (Fin 13))) _ _
      (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> decide
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)]; rfl)
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (hR 3 6 (by decide)) hX hY
  have P02 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 D →
      D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 5} : Finset (Fin 13))) : Finset (Fin 13))) = false → D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 7} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 7} : Finset (Fin 13))) : Finset (Fin 13))) = false → False := by
    intro D ho hR hX hY
    exact PEqualNP.Outside.Kit.rejAcc D ho (PEqualNP.GenericRejection.incidenceInput ({7} : Finset (Fin 13)) ({7} : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput ({7} : Finset (Fin 13)) (∅ : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({7} : Finset (Fin 13))) _ _
      (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> decide
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)]; rfl)
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (hR 7 7 (by decide)) hX hY
  have P12 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 D →
      D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 6} : Finset (Fin 13))) : Finset (Fin 13))) = false → D.eval (PEqualNP.GenericRejection.incidenceInput ({0, 1, 2, 7} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0, 1, 2, 7} : Finset (Fin 13))) : Finset (Fin 13))) = false → False := by
    intro D ho hR hX hY
    exact PEqualNP.Outside.Kit.rejAcc D ho (PEqualNP.GenericRejection.incidenceInput ({7} : Finset (Fin 13)) ({7} : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput ({7} : Finset (Fin 13)) (∅ : Finset (Fin 13))) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({7} : Finset (Fin 13))) _ _
      (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> decide
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)]; rfl)
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (by simp [PEqualNP.GenericRejection.incidenceInput])
      (by
        intro i hi
        rcases Nat.lt_or_ge i 26 with h | h
        · interval_cases i <;> revert hi <;> decide +kernel
        · rw [PEqualNP.Outside.Kit.getD_past _ i (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at hi; exact absurd hi (by decide))
      (hR 7 7 (by decide)) hX hY
  have q0 := hq ({0, 1, 2, 5} : Finset (Fin 13)) (by decide +kernel)
  have q1 := hq ({0, 1, 2, 6} : Finset (Fin 13)) (by decide +kernel)
  have q2 := hq ({0, 1, 2, 7} : Finset (Fin 13)) (by decide +kernel)
  rcases q0 with a0 | a0 <;> rcases q1 with a1 | a1 <;> rcases q2 with a2 | a2 <;>
    first | exact P01 ⟨C.gates, x2⟩ onlyOr hR2 a0 a1 | exact P01 ⟨C.gates, x3⟩ onlyOr hR3 a0 a1 | exact P02 ⟨C.gates, x2⟩ onlyOr hR2 a0 a2 | exact P02 ⟨C.gates, x3⟩ onlyOr hR3 a0 a2 | exact P12 ⟨C.gates, x2⟩ onlyOr hR2 a1 a2 | exact P12 ⟨C.gates, x3⟩ onlyOr hR3 a1 a2
