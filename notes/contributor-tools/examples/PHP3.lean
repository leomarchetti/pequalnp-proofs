-- The resolution checker and its soundness proof are adapted from L_pcx_171.lean.
import Mathlib
import PEqualNP.Defs

namespace ProofComplexityBenchmark3

open PEqualNP.ProofComplexity

theorem memD {α : Type} (l : List α) (d : α) (i : ℕ) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

-- resolution lines, newest first; a hint (i, j, v): the premises are entries i and j of the tail, pivot v
def chkR {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => true
  | (R, none) :: t => ax R && chkR ax t
  | (R, some (i, j, v)) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((v, true) ∈ (t.map Prod.fst).getD i ∅ ∧ (v, false) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (v, true) ∪ ((t.map Prod.fst).getD j ∅).erase (v, false)) &&
      chkR ax t

theorem chkR_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkR ax l = true → IsDerivation F (l.map Prod.fst)
  | [], _ => IsDerivation.nil
  | (R, none) :: t, h => by
    simp only [chkR, Bool.and_eq_true] at h
    exact IsDerivation.ax (chkR_sound F ax hax t h.2) (hax R h.1)
  | (R, some (i, j, v)) :: t, h => by
    simp only [chkR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsDerivation.res (chkR_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨v, h1, h2, h3⟩

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def cert : List (Clause (Fin 4 × Fin 3) × Option (ℕ × ℕ × (Fin 4 × Fin 3))) := [
  (∅, some (3, 0, (3, 2))),
  ({((3, 2), false)}, some (0, 34, (2, 2))),
  ({((2, 2), true), ((3, 2), false)}, some (0, 34, (1, 2))),
  ({((1, 2), true), ((2, 2), true), ((3, 2), false)}, some (20, 35, (0, 2))),
  ({((3, 2), true)}, some (3, 0, (3, 1))),
  ({((3, 1), false)}, some (0, 36, (2, 1))),
  ({((2, 1), true), ((3, 1), false)}, some (0, 36, (1, 1))),
  ({((1, 1), true), ((2, 1), true), ((3, 1), false)}, some (10, 37, (0, 1))),
  ({((3, 1), true), ((3, 2), true)}, some (45, 0, (3, 0))),
  ({((3, 0), false)}, some (0, 38, (2, 0))),
  ({((2, 0), true), ((3, 0), false)}, some (0, 38, (1, 0))),
  ({((1, 0), true), ((2, 0), true), ((3, 0), false)}, some (0, 39, (0, 0))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true)}, some (2, 0, (2, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 2), false)}, some (0, 24, (1, 2))),
  ({((0, 0), true), ((1, 0), true), ((1, 2), true), ((2, 2), false)}, some (17, 25, (0, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 2), true)}, some (39, 0, (2, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 1), false)}, some (0, 27, (1, 1))),
  ({((0, 0), true), ((1, 0), true), ((1, 1), true), ((2, 1), false)}, some (12, 28, (0, 1))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true)}, some (2, 0, (2, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 2), false)}, some (0, 18, (1, 2))),
  ({((0, 1), true), ((1, 1), true), ((1, 2), true), ((2, 2), false)}, some (13, 19, (0, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 2), true)}, some (33, 0, (2, 0))),
  ({((0, 1), true), ((1, 1), true), ((2, 0), false)}, some (0, 27, (1, 0))),
  ({((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), false)}, some (6, 28, (0, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true)}, some (2, 0, (2, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 1), false)}, some (0, 18, (1, 1))),
  ({((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), false)}, some (7, 19, (0, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 1), true), ((2, 2), true)}, some (27, 0, (2, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 0), false)}, some (0, 21, (1, 0))),
  ({((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), false)}, some (2, 22, (0, 0))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true)}, some (25, 0, (1, 2))),
  ({((0, 0), true), ((0, 1), true), ((1, 2), false)}, some (25, 9, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true)}, some (23, 0, (1, 1))),
  ({((0, 0), true), ((0, 2), true), ((1, 1), false)}, some (23, 13, (0, 1))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true)}, some (21, 0, (1, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 0), false)}, some (21, 17, (0, 0))),
  ({((2, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((3, 2), false)}, none),
  ({((0, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((1, 2), false)}, none),
  ({((2, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((3, 1), false)}, none),
  ({((0, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((1, 1), false)}, none),
  ({((2, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((3, 0), false)}, none),
  ({((0, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((1, 0), false)}, none),
  ({((3, 0), true), ((3, 1), true), ((3, 2), true)}, none),
  ({((2, 0), true), ((2, 1), true), ((2, 2), true)}, none),
  ({((1, 0), true), ((1, 1), true), ((1, 2), true)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true)}, none)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : chkR (axPHP 4 3) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exists_refutation : ∃ π : List (Clause (Fin 4 × Fin 3)), IsRefutation (PHP 4 3) π ∧ π.length ≤ 58 := by
  exact ⟨cert.map Prod.fst,
    ⟨chkR_sound _ (axPHP 4 3) (axPHP_sound 4 3) _ checked, by decide +kernel⟩,
    by decide +kernel⟩

end ProofComplexityBenchmark3

#print axioms ProofComplexityBenchmark3.exists_refutation
