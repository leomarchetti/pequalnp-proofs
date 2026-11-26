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



def F8752 (X Y : Finset (Fin 13)) : Fin 26 → Bool := fun x8 =>
  if (x8 : ℕ) < 13 then decide (Fin.ofNat 13 (x8 : ℕ) ∈ X) else decide (Fin.ofNat 13 (x8 : ℕ) ∈ Y)

def G8752 (C : Circuit) (l : List ℕ) (X Y : Finset (Fin 13)) : Bool :=
  GateOp.or.eval (l.map fun k => (C.wires (List.ofFn (F8752 X Y))).getD k false)

lemma wiresSplit {n : ℕ} (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x y z : Fin n → Bool) (hz : ∀ i, z i = (x i || y i)) (k : ℕ) :
    (C.wires (List.ofFn z)).getD k false =
      ((C.wires (List.ofFn x)).getD k false || (C.wires (List.ofFn y)).getD k false) := by
  have hz' : z = fun i => x i || y i := funext hz
  subst hz'
  unfold Circuit.wires
  refine wire_split C.gates ho _ _ _ (by simp) (by simp) ?_ k
  intro i
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

lemma orMapSplit (l : List ℕ) (f g h : ℕ → Bool) (hh : ∀ k, h k = (f k || g k)) :
    GateOp.or.eval (l.map h) = (GateOp.or.eval (l.map f) || GateOp.or.eval (l.map g)) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      rw [ih, hh a]
      cases f a <;> cases g a <;> simp

lemma Gsplit (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (l : List ℕ)
    (X1 Y1 X2 Y2 X Y : Finset (Fin 13))
    (h : ∀ i, F8752 X Y i = (F8752 X1 Y1 i || F8752 X2 Y2 i)) :
    G8752 C l X Y = (G8752 C l X1 Y1 || G8752 C l X2 Y2) := by
  unfold G8752
  exact orMapSplit l _ _ _ (wiresSplit C ho _ _ _ h)

lemma Gmono (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (l : List ℕ)
    (X1 Y1 X Y : Finset (Fin 13)) (hX : X1 ⊆ X) (hY : Y1 ⊆ Y)
    (h1 : G8752 C l X1 Y1 = true) : G8752 C l X Y = true := by
  have e := Gsplit C ho l X1 Y1 X Y X Y (by
    intro i
    unfold F8752
    split
    · generalize Fin.ofNat 13 (i : ℕ) = a
      by_cases hm : a ∈ X1
      · rw [decide_eq_true hm, decide_eq_true (hX hm)]; rfl
      · rw [decide_eq_false hm, Bool.false_or]
    · generalize Fin.ofNat 13 (i : ℕ) = a
      by_cases hm : a ∈ Y1
      · rw [decide_eq_true hm, decide_eq_true (hY hm)]; rfl
      · rw [decide_eq_false hm, Bool.false_or])
  rw [e, h1]; rfl

end PEqualNP.Outside.Kit

set_option maxRecDepth 20000 in
theorem child_8752 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (50 : ℕ) ≤ {x6 : ℕ | ∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C l hM hNo _ hcond
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  obtain ⟨hA, hB⟩ := hcond
  have h1 : PEqualNP.Outside.Kit.G8752 C l {0} {0} = true := hA 0 0 (by decide)
  have hB1 := (hB {0} (by decide)).1
  have hB2 := (hB {0} (by decide)).2
  have hs := PEqualNP.Outside.Kit.Gsplit C onlyOr l {0} ∅ ∅ {0} {0} {0} (by
    intro i; unfold PEqualNP.Outside.Kit.F8752; split <;> simp)
  rw [h1] at hs
  exfalso
  cases hx : PEqualNP.Outside.Kit.G8752 C l {0} ∅
  · rw [hx, Bool.false_or] at hs
    exact Bool.false_ne_true (hB2.symm.trans
      (PEqualNP.Outside.Kit.Gmono C onlyOr l ∅ {0} _ {0} (Finset.empty_subset _) (Finset.Subset.refl _) hs.symm))
  · exact Bool.false_ne_true (hB1.symm.trans
      (PEqualNP.Outside.Kit.Gmono C onlyOr l {0} ∅ {0} _ (Finset.Subset.refl _) (Finset.empty_subset _) hx))
