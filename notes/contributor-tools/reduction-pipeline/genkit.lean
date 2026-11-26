import PEqualNP.Defs

namespace PEqualNP.Outside.GenKit
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



theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp


/-- Generalised connectivity bound: a fan-in-two circuit whose output depends on every input in
`E` (inputs below `n`) has at least `E.card - 1` gates. -/
theorem boundE (n : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (E : Finset ℕ)
    (hEn : ∀ i ∈ E, i < n)
    (hdep : ∀ i ∈ E, ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) :
    E.card ≤ C.size + 1 := by
  let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have hsub : E ⊆ S := by
    intro i hiE
    have hi := hEn i hiE
    by_contra hni
    obtain ⟨x, hx, hne⟩ := hdep i hiE
    apply hne
    let y := x.set i (!(x.getD i false))
    have hy : y.length = n := by simp [y, hx]
    have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y D0
      (by simp [D0, hx]) (by simp [D0, hy]) ?_ C.output ?_
    · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq, wires_eq]; exact key
    · intro w hw
      by_cases hwn : w < n
      · apply hw w
        simp [D0, List.getD_eq_getElem?_getD, hwn]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · intro j hj
      have hji : j ≠ i := fun e => hni (e ▸ hj)
      simp only [y]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hji)]
  have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have := Finset.card_le_card hsub
  change E.card ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at this
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega

/-- Bridge from an `iff` characterisation: if `R (e_j)` fails and `R (e_j ∨ e_i)` holds, input `i`
is essential. -/
theorem ess_of_pair {n : ℕ} (C : Circuit) (R : (Fin n → Bool) → Prop)
    (hiff : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ R x) (i j : Fin n) (hij : i ≠ j)
    (h0 : ¬ R (fun k => decide (k = j))) (h1 : R (fun k => decide (k = j ∨ k = i))) :
    ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false))) := by
  refine ⟨List.ofFn (fun k : Fin n => decide (k = j)), by simp, ?_⟩
  have hset : (List.ofFn (fun k : Fin n => decide (k = j))).set i
      (!((List.ofFn (fun k : Fin n => decide (k = j))).getD i false)) =
      List.ofFn (fun k : Fin n => decide (k = j ∨ k = i)) := by
    apply List.ext_getElem
    · simp
    · intro m h1' h2'
      simp only [List.getElem_set, List.getElem_ofFn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn]
      by_cases hm : (i : ℕ) = m
      · subst hm; simp [hij]
      · rw [if_neg hm]
        have : (⟨m, by simpa using h2'⟩ : Fin n) ≠ i := fun e => hm (by rw [← e])
        simp [this]
  rw [hset]
  intro he
  have a := (hiff (fun k => decide (k = j ∨ k = i))).mpr h1
  have b : C.eval (List.ofFn fun k : Fin n => decide (k = j)) ≠ true := fun h => h0 ((hiff _).mp h)
  exact b (he ▸ a)


/-- Reading a wire below the input length returns the input bit (gates only append). -/
theorem wires_prefix (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq]
  generalize C.gates = gs
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (wstep x g) (by simp [wstep]; omega)]
      simp only [wstep]
      rw [getD_snoc, if_pos hi]

end PEqualNP.Outside.GenKit
