import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19147.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Move a gate wire index past `N - M` extra wires; input indices (below `M`) stay. -/
def shiftIdx (M N i : ℕ) : ℕ := if i < M then i else i + (N - M)

/-- A gate with its wire indices moved by `shiftIdx`. -/
def shiftGate (M N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx M N)⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (x : List Bool),
    ∃ t : List Bool, gs.foldl step x = x ++ t ∧ t.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro x; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht, hl⟩ := ih (step x g)
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ t, ?_, by simp [hl]⟩
    simp only [List.foldl_cons]
    rw [ht]
    simp [step]

theorem getD_shift (M N : ℕ) (T u : List Bool) (hM : M ≤ N) (hT : T.length = N) (i : ℕ) :
    (T ++ u).getD (shiftIdx M N i) false = (T.take M ++ u).getD i false := by
  have hTM : (T.take M).length = M := by simp [hT, hM]
  unfold shiftIdx
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hT, hTM]
    congr 2
    omega

theorem fold_shift (M N : ℕ) (T : List Bool) (hM : M ≤ N) (hT : T.length = N) :
    ∀ (gs : List Gate) (u : List Bool), ∃ u' : List Bool,
      (gs.map (shiftGate M N)).foldl step (T ++ u) = T ++ u' ∧
      gs.foldl step (T.take M ++ u) = T.take M ++ u' := by
  intro gs
  induction gs with
  | nil => intro u; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u
    have key : (g.inputs.map (shiftIdx M N)).map (fun i => (T ++ u).getD i false)
        = g.inputs.map (fun i => (T.take M ++ u).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_shift M N T u hM hT i)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [g.op.eval (g.inputs.map fun i => (T.take M ++ u).getD i false)])
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons]
      have : step (T ++ u) (shiftGate M N g)
          = T ++ (u ++ [g.op.eval (g.inputs.map fun i => (T.take M ++ u).getD i false)]) := by
        simp only [step, shiftGate]
        rw [key, List.append_assoc]
      rw [this]
      exact h1
    · simp only [List.foldl_cons]
      have : step (T.take M ++ u) g
          = T.take M ++ (u ++ [g.op.eval (g.inputs.map fun i => (T.take M ++ u).getD i false)]) := by
        simp only [step, List.append_assoc]
      rw [this]
      exact h2

/-- A's gates, then B's gates moved past A's, then `p = a OR b`, `q = a AND b`, `r = NOT q`,
`out = p AND r`. An output wire that does not exist is replaced by an index past the end. -/
def xorCirc (M : ℕ) (A B : Circuit) : Circuit :=
  let N := M + A.gates.length
  let L := N + B.gates.length
  let a := if A.output < N then A.output else L + 4
  let b := if B.output < M + B.gates.length then shiftIdx M N B.output else L + 4
  ⟨A.gates ++ B.gates.map (shiftGate M N) ++
    [⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [a, b]⟩, ⟨GateOp.not, [L + 1]⟩, ⟨GateOp.and, [L, L + 2]⟩],
    L + 3⟩

theorem getD_past (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_app_left (w r : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ r).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (w r : List Bool) (j : ℕ) :
    (w ++ r).getD (w.length + j) false = r.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem getD_stable (w r : List Bool) (i : ℕ) (h : i < w.length ∨ w.length + r.length ≤ i) :
    (w ++ r).getD i false = w.getD i false := by
  rcases h with h | h
  · exact getD_app_left w r i h
  · rw [getD_past _ _ (by simp; omega), getD_past _ _ (by omega)]

/-- The four-gate tail computes the exclusive OR of the two wires it reads. -/
theorem tail_xor (W : List Bool) (a b L : ℕ) (hL : W.length = L)
    (ha : a < L ∨ L + 4 ≤ a) (hb : b < L ∨ L + 4 ≤ b) :
    (([⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [a, b]⟩, ⟨GateOp.not, [L + 1]⟩,
      ⟨GateOp.and, [L, L + 2]⟩] : List Gate).foldl step W).getD (L + 3) false
      = xor (W.getD a false) (W.getD b false) := by
  set va := W.getD a false with hva
  set vb := W.getD b false with hvb
  have s1 : ∀ r : List Bool, r.length ≤ 3 → (W ++ r).getD a false = va := fun r hr =>
    getD_stable W r a (by rcases ha with h | h <;> [left; right] <;> omega)
  have s2 : ∀ r : List Bool, r.length ≤ 3 → (W ++ r).getD b false = vb := fun r hr =>
    getD_stable W r b (by rcases hb with h | h <;> [left; right] <;> omega)
  simp only [List.foldl_cons, List.foldl_nil, step]
  have e0a : W.getD a false = va := rfl
  have e0b : W.getD b false = vb := rfl
  have e1a := s1 [va || vb] (by simp)
  have e1b := s2 [va || vb] (by simp)
  simp only [List.map_cons, List.map_nil, GateOp.eval, e0a, e0b]
  simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.or_false,
    Bool.and_true, List.headD_cons]
  rw [e1a, e1b]
  have r1 : (W ++ [va || vb] ++ [va && vb]).getD (L + 1) false = (va && vb) := by
    rw [List.append_assoc, ← hL, getD_app_right]
    rfl
  rw [r1]
  have r2 : (W ++ [va || vb] ++ [va && vb] ++ [!(va && vb)]).getD L false = (va || vb) := by
    rw [List.append_assoc, List.append_assoc, ← hL, show W.length = W.length + 0 from rfl,
      getD_app_right]
    rfl
  have r3 : (W ++ [va || vb] ++ [va && vb] ++ [!(va && vb)]).getD (L + 2) false = !(va && vb) := by
    rw [List.append_assoc, List.append_assoc, ← hL, getD_app_right]
    rfl
  rw [r2, r3]
  have r4 : (W ++ [va || vb] ++ [va && vb] ++ [!(va && vb)] ++ [(va || vb) && !(va && vb)]).getD
      (L + 3) false = ((va || vb) && !(va && vb)) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc, ← hL, getD_app_right]
    rfl
  rw [r4]
  cases va <;> cases vb <;> rfl

theorem eval_xorCirc (M : ℕ) (A B : Circuit) (x : List Bool) (hx : x.length = M) :
    (xorCirc M A B).eval x = xor (A.eval x) (B.eval x) := by
  obtain ⟨tA, hA, hlA⟩ := fold_prefix A.gates x
  set T := x ++ tA with hTdef
  have hTl : T.length = M + A.gates.length := by simp [hTdef, hx, hlA]
  have hTM : T.take M = x := by
    rw [hTdef, List.take_append_of_le_length (by omega)]
    simp [← hx]
  obtain ⟨u', h1, h2⟩ := fold_shift M (M + A.gates.length) T (by omega) hTl B.gates []
  simp only [List.append_nil, hTM] at h1 h2
  obtain ⟨tB, hB, hlB⟩ := fold_prefix B.gates x
  have hu' : u' = tB := by
    have := h2.symm.trans hB
    exact List.append_cancel_left this
  subst hu'
  have hWl : (T ++ u').length = M + A.gates.length + B.gates.length := by
    simp [hTl, hlB]
  -- the value read for A's output
  have hva : (T ++ u').getD (if A.output < M + A.gates.length then A.output
      else M + A.gates.length + B.gates.length + 4) false = A.eval x := by
    rw [show A.eval x = (A.gates.foldl step x).getD A.output false from rfl, hA]
    split_ifs with h
    · rw [getD_app_left T u' _ (by omega)]
    · rw [getD_past _ _ (by omega), getD_past _ _ (by rw [hTl]; omega)]
  -- the value read for B's output
  have hvb : (T ++ u').getD (if B.output < M + B.gates.length
      then shiftIdx M (M + A.gates.length) B.output
      else M + A.gates.length + B.gates.length + 4) false = B.eval x := by
    rw [show B.eval x = (B.gates.foldl step x).getD B.output false from rfl, hB]
    split_ifs with h
    · rw [getD_shift M (M + A.gates.length) T u' (by omega) hTl, hTM]
    · rw [getD_past _ _ (by omega), getD_past _ _ (by simp [hx, hlB]; omega)]
  rw [← hva, ← hvb]
  have hw : (xorCirc M A B).eval x =
      ((([⟨GateOp.or, [(if A.output < M + A.gates.length then A.output
          else M + A.gates.length + B.gates.length + 4),
          (if B.output < M + B.gates.length then shiftIdx M (M + A.gates.length) B.output
          else M + A.gates.length + B.gates.length + 4)]⟩,
        ⟨GateOp.and, [(if A.output < M + A.gates.length then A.output
          else M + A.gates.length + B.gates.length + 4),
          (if B.output < M + B.gates.length then shiftIdx M (M + A.gates.length) B.output
          else M + A.gates.length + B.gates.length + 4)]⟩,
        ⟨GateOp.not, [M + A.gates.length + B.gates.length + 1]⟩,
        ⟨GateOp.and, [M + A.gates.length + B.gates.length,
          M + A.gates.length + B.gates.length + 2]⟩] : List Gate).foldl step (T ++ u')).getD
        (M + A.gates.length + B.gates.length + 3) false) := by
    show ((xorCirc M A B).gates.foldl step x).getD _ false = _
    simp only [xorCirc, List.foldl_append]
    rw [hA, h1]
  rw [hw]
  apply tail_xor _ _ _ _ hWl
  · split_ifs <;> omega
  · split_ifs with h
    · left; unfold shiftIdx; split_ifs <;> omega
    · right; omega

end PEqualNP.Outside.L_meta_19147.Helpers

open PEqualNP.Outside.L_meta_19147.Helpers in
theorem PEqualNP.Outside.L_meta_19147 : ∀ (n m s t : ℕ) (A B : Fin n → Fin m → Bool),
    PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost B t →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s + t + 4 ∧
      PEqualNP.Represents.Represents (fun u v => xor (A u v) (B u v)) C := by
  intro n m s t A B ⟨CA, hmA, hsA, hrA⟩ ⟨CB, hmB, hsB, hrB⟩
  refine ⟨xorCirc (n + m) CA CB, ?_, ?_, ?_⟩
  · intro g hg
    simp only [xorCirc, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | hg
    · obtain ⟨h1, h2⟩ := hmA g hg
      refine ⟨?_, h2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      rcases h1 with h1 | h1 <;> simp [h1]
    · obtain ⟨h1, h2⟩ := hmB g0 hg0
      refine ⟨?_, by simpa [shiftGate] using h2⟩
      simp only [shiftGate, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      rcases h1 with h1 | h1 <;> simp [h1]
    · rcases hg with rfl | rfl | rfl | rfl <;> simp
  · simp only [xorCirc, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append,
      List.length_map, List.length_cons, List.length_nil]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hsA hsB
    omega
  · intro u v
    rw [eval_xorCirc (n + m) CA CB _ (by simp [PEqualNP.Represents.oneEach]), hrA u v, hrB u v]
