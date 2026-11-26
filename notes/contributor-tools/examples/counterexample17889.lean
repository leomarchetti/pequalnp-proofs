import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17889

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private def edges : Finset (Fin 2 × Fin 2) := Finset.univ
private def erased := edges.erase (0, 0)

private def value (E : Finset (Fin 2 × Fin 2)) (x : Fin 4 → Bool) : Bool :=
  decide (∃ a b : Fin 2, (a,b) ∈ E ∧ x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true)

private def gate (op : Bool) (a b : ℕ) : Gate :=
  ⟨if op then .and else .or, [a,b]⟩

private def complete : Circuit := ⟨[gate false 0 1, gate false 2 3, gate true 4 5], 6⟩

private theorem completeOK : IsAO2 4 complete ∧ ∀ x, circuitFun 4 complete x = value edges x := by
  decide +kernel

private theorem normGate {k : ℕ} (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (hread : ∀ i ∈ g.inputs, i < k) :
    ∃ (o : Bool) (a b : Fin k), g = gate o a.val b.val := by
  cases g with
  | mk op inputs =>
    obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    let a' : Fin k := ⟨a, hread a (by simp)⟩
    let b' : Fin k := ⟨b, hread b (by simp)⟩
    rcases hop with rfl | rfl
    · exact ⟨true, a', b', rfl⟩
    · exact ⟨false, a', b', rfl⟩

private theorem zeroImpossible (out : Fin 4) :
    ¬ ∀ x, circuitFun 4 ⟨[],out.val⟩ x = value erased x := by
  fin_cases out <;> decide +kernel

private theorem oneImpossible :
    ∀ (s : Bool) (a b : Fin 4) (out : Fin 5),
      ¬ ∀ x, circuitFun 4 ⟨[gate s a.val b.val],out.val⟩ x = value erased x := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem twoImpossible (s : Bool) (a b : Fin 4) :
    ∀ (t : Bool) (c d : Fin 5) (out : Fin 6),
      ¬ ∀ x, circuitFun 4 ⟨[gate s a.val b.val,gate t c.val d.val],out.val⟩ x = value erased x := by
  cases s <;> fin_cases a <;> fin_cases b <;> decide +kernel

private theorem wiresLength (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
      unfold Circuit.wires at *
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp
      omega

private theorem noSmall (C : Circuit) (small : C.size < 3) (hao : IsAO2 4 C)
    (compute : ∀ x, circuitFun 4 C x = value erased x) : False := by
  obtain ⟨gs, out⟩ := C
  have hout : out < 4 + gs.length := by
    by_contra! hout
    have h := compute (fun _ => true)
    have hr : value erased (fun _ => true) = true := by decide +kernel
    rw [hr] at h
    change (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun _ : Fin 4 => true))).getD out false = true at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none] at h
    · contradiction
    · simpa [wiresLength] using hout
  obtain ⟨ops, back, arity⟩ := hao
  change gs.length < 3 at small
  cases gs with
  | nil => exact zeroImpossible ⟨out, by simpa using hout⟩ compute
  | cons g gs =>
    have hg : ∃ (s : Bool) (a b : Fin 4), g = gate s a.val b.val :=
      normGate g (ops g (by simp)) (arity g (by simp)) (by
        intro i hi
        exact back 0 (by simp) i hi)
    obtain ⟨s,a,b,rfl⟩ := hg
    cases gs with
    | nil => exact oneImpossible s a b ⟨out, by simpa using hout⟩ compute
    | cons g gs =>
      have he : gs = [] := by
        simp at small
        simpa using (show gs.length = 0 by omega)
      subst gs
      have hg : ∃ (t : Bool) (c d : Fin 5), g = gate t c.val d.val :=
        normGate g (ops g (by simp)) (arity g (by simp)) (by
          intro i hi
          exact back 1 (by simp) i hi)
      obtain ⟨t,c,d,rfl⟩ := hg
      exact twoImpossible s a b t c d ⟨out, by simpa using hout⟩ compute

end PEqualNP.Outside.L_meta_17889

open PEqualNP.Outside.L_meta_17889

theorem PEqualNP.Outside.L_meta_17889 : ¬ (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Fin x1 × Fin x2) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4 ∈ x3 → (fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) x3 x5 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size < x5.size ∧ (fun (x9 : Finset (Fin x1 × Fin x2)) (x10 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x10 ∧ ∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x10 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x9 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) (x3.erase x4) x8) := by
  intro h
  obtain ⟨C, hsmall, hao, hval⟩ := h 2 2 edges (0,0) complete (by simp [edges]) completeOK
  exact noSmall C hsmall hao hval