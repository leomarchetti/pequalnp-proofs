-- The resolution checker and its soundness proof are adapted from L_pcx_171.lean.
import Mathlib
import PEqualNP.Defs

namespace ProofComplexityBenchmark4

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

def cert : List (Clause (Fin 5 × Fin 4) × Option (ℕ × ℕ × (Fin 5 × Fin 4))) := [
  (∅, some (4, 0, (4, 3))),
  ({((4, 3), false)}, some (0, 110, (3, 3))),
  ({((3, 3), true), ((4, 3), false)}, some (0, 110, (2, 3))),
  ({((2, 3), true), ((3, 3), true), ((4, 3), false)}, some (0, 111, (1, 3))),
  ({((1, 3), true), ((2, 3), true), ((3, 3), true), ((4, 3), false)}, some (51, 113, (0, 3))),
  ({((4, 3), true)}, some (4, 0, (4, 2))),
  ({((4, 2), false)}, some (0, 115, (3, 2))),
  ({((3, 2), true), ((4, 2), false)}, some (0, 115, (2, 2))),
  ({((2, 2), true), ((3, 2), true), ((4, 2), false)}, some (0, 116, (1, 2))),
  ({((1, 2), true), ((2, 2), true), ((3, 2), true), ((4, 2), false)}, some (34, 118, (0, 2))),
  ({((4, 2), true), ((4, 3), true)}, some (4, 0, (4, 1))),
  ({((4, 1), false)}, some (0, 120, (3, 1))),
  ({((3, 1), true), ((4, 1), false)}, some (0, 120, (2, 1))),
  ({((2, 1), true), ((3, 1), true), ((4, 1), false)}, some (0, 121, (1, 1))),
  ({((1, 1), true), ((2, 1), true), ((3, 1), true), ((4, 1), false)}, some (17, 123, (0, 1))),
  ({((4, 1), true), ((4, 2), true), ((4, 3), true)}, some (136, 0, (4, 0))),
  ({((4, 0), false)}, some (0, 125, (3, 0))),
  ({((3, 0), true), ((4, 0), false)}, some (0, 125, (2, 0))),
  ({((2, 0), true), ((3, 0), true), ((4, 0), false)}, some (0, 126, (1, 0))),
  ({((1, 0), true), ((2, 0), true), ((3, 0), true), ((4, 0), false)}, some (0, 128, (0, 0))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true)}, some (3, 0, (3, 3))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 3), false)}, some (0, 92, (2, 3))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)}, some (0, 93, (1, 3))),
  ({((0, 0), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 3), false)}, some (56, 95, (0, 3))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 3), true)}, some (3, 0, (3, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 2), false)}, some (0, 98, (2, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)}, some (0, 99, (1, 2))),
  ({((0, 0), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 2), false)}, some (46, 101, (0, 2))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 0), true), ((3, 2), true), ((3, 3), true)}, some (124, 0, (3, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((3, 1), false)}, some (0, 104, (2, 1))),
  ({((0, 0), true), ((1, 0), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)}, some (0, 105, (1, 1))),
  ({((0, 0), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 1), false)}, some (36, 107, (0, 1))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true)}, some (3, 0, (3, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 3), false)}, some (0, 80, (2, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)}, some (0, 81, (1, 3))),
  ({((0, 1), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 3), false)}, some (56, 83, (0, 3))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 3), true)}, some (3, 0, (3, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 2), false)}, some (0, 86, (2, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)}, some (0, 87, (1, 2))),
  ({((0, 1), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 2), false)}, some (46, 89, (0, 2))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (112, 0, (3, 0))),
  ({((0, 1), true), ((1, 1), true), ((2, 1), true), ((3, 0), false)}, some (0, 102, (2, 0))),
  ({((0, 1), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)}, some (0, 103, (1, 0))),
  ({((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((3, 0), false)}, some (24, 105, (0, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true)}, some (3, 0, (3, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 3), false)}, some (0, 68, (2, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)}, some (0, 69, (1, 3))),
  ({((0, 2), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 3), false)}, some (50, 71, (0, 3))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 2), true), ((3, 3), true)}, some (3, 0, (3, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), false)}, some (0, 84, (2, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)}, some (0, 85, (1, 1))),
  ({((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 1), false)}, some (34, 87, (0, 1))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (100, 0, (3, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 2), true), ((3, 0), false)}, some (0, 90, (2, 0))),
  ({((0, 2), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)}, some (0, 91, (1, 0))),
  ({((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((3, 0), false)}, some (18, 93, (0, 0))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 3), true)}, some (3, 0, (3, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), false)}, some (0, 66, (2, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)}, some (0, 67, (1, 2))),
  ({((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true), ((3, 2), false)}, some (38, 69, (0, 2))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 2), true), ((3, 3), true)}, some (3, 0, (3, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), false)}, some (0, 72, (2, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)}, some (0, 73, (1, 1))),
  ({((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true), ((3, 1), false)}, some (28, 75, (0, 1))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, some (88, 0, (3, 0))),
  ({((0, 3), true), ((1, 3), true), ((2, 3), true), ((3, 0), false)}, some (0, 78, (2, 0))),
  ({((0, 3), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)}, some (0, 79, (1, 0))),
  ({((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true), ((3, 0), false)}, some (12, 81, (0, 0))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true)}, some (2, 0, (2, 3))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 3), false)}, some (0, 47, (1, 3))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 3), false)}, some (35, 49, (0, 3))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 0), true), ((2, 1), true), ((2, 3), true)}, some (82, 0, (2, 2))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((2, 2), false)}, some (0, 54, (1, 2))),
  ({((0, 0), true), ((0, 1), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 2), false)}, some (30, 56, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true)}, some (2, 0, (2, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 3), false)}, some (0, 41, (1, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)}, some (31, 43, (0, 3))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)}, some (76, 0, (2, 1))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 2), true), ((2, 1), false)}, some (0, 58, (1, 1))),
  ({((0, 0), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 1), false)}, some (24, 60, (0, 1))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 3), true)}, some (2, 0, (2, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 2), false)}, some (0, 45, (1, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)}, some (25, 47, (0, 2))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 0), true), ((2, 2), true), ((2, 3), true)}, some (70, 0, (2, 1))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 3), true), ((2, 1), false)}, some (0, 52, (1, 1))),
  ({((0, 0), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 1), false)}, some (20, 54, (0, 1))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true)}, some (2, 0, (2, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 3), false)}, some (0, 29, (1, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 3), false)}, some (21, 31, (0, 3))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (64, 0, (2, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)}, some (0, 56, (1, 0))),
  ({((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true), ((2, 0), false)}, some (12, 58, (0, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 3), true)}, some (2, 0, (2, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 2), false)}, some (0, 33, (1, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 2), false)}, some (15, 35, (0, 2))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (58, 0, (2, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)}, some (0, 50, (1, 0))),
  ({((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true), ((2, 0), false)}, some (8, 52, (0, 0))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 2), true), ((2, 3), true)}, some (2, 0, (2, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)}, some (0, 37, (1, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true), ((2, 1), false)}, some (9, 39, (0, 1))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, some (52, 0, (2, 0))),
  ({((0, 2), true), ((0, 3), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)}, some (0, 44, (1, 0))),
  ({((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true), ((2, 0), false)}, some (4, 46, (0, 0))),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 0), true), ((1, 1), true), ((1, 2), true)}, some (50, 0, (1, 3))),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((1, 3), false)}, some (50, 15, (0, 3))),
  ({((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 0), true), ((1, 1), true), ((1, 3), true)}, some (48, 0, (1, 2))),
  ({((0, 0), true), ((0, 1), true), ((0, 3), true), ((1, 2), false)}, some (48, 23, (0, 2))),
  ({((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 0), true), ((1, 2), true), ((1, 3), true)}, some (46, 0, (1, 1))),
  ({((0, 0), true), ((0, 2), true), ((0, 3), true), ((1, 1), false)}, some (46, 31, (0, 1))),
  ({((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}, some (44, 0, (1, 0))),
  ({((0, 1), true), ((0, 2), true), ((0, 3), true), ((1, 0), false)}, some (44, 39, (0, 0))),
  ({((3, 3), false), ((4, 3), false)}, none),
  ({((2, 3), false), ((4, 3), false)}, none),
  ({((2, 3), false), ((3, 3), false)}, none),
  ({((1, 3), false), ((4, 3), false)}, none),
  ({((1, 3), false), ((3, 3), false)}, none),
  ({((1, 3), false), ((2, 3), false)}, none),
  ({((0, 3), false), ((4, 3), false)}, none),
  ({((0, 3), false), ((3, 3), false)}, none),
  ({((0, 3), false), ((2, 3), false)}, none),
  ({((0, 3), false), ((1, 3), false)}, none),
  ({((3, 2), false), ((4, 2), false)}, none),
  ({((2, 2), false), ((4, 2), false)}, none),
  ({((2, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((4, 2), false)}, none),
  ({((1, 2), false), ((3, 2), false)}, none),
  ({((1, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((4, 2), false)}, none),
  ({((0, 2), false), ((3, 2), false)}, none),
  ({((0, 2), false), ((2, 2), false)}, none),
  ({((0, 2), false), ((1, 2), false)}, none),
  ({((3, 1), false), ((4, 1), false)}, none),
  ({((2, 1), false), ((4, 1), false)}, none),
  ({((2, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((4, 1), false)}, none),
  ({((1, 1), false), ((3, 1), false)}, none),
  ({((1, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((4, 1), false)}, none),
  ({((0, 1), false), ((3, 1), false)}, none),
  ({((0, 1), false), ((2, 1), false)}, none),
  ({((0, 1), false), ((1, 1), false)}, none),
  ({((3, 0), false), ((4, 0), false)}, none),
  ({((2, 0), false), ((4, 0), false)}, none),
  ({((2, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((4, 0), false)}, none),
  ({((1, 0), false), ((3, 0), false)}, none),
  ({((1, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((4, 0), false)}, none),
  ({((0, 0), false), ((3, 0), false)}, none),
  ({((0, 0), false), ((2, 0), false)}, none),
  ({((0, 0), false), ((1, 0), false)}, none),
  ({((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)}, none),
  ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)}, none),
  ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)}, none),
  ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)}, none),
  ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)}, none)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : chkR (axPHP 5 4) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exists_refutation : ∃ π : List (Clause (Fin 5 × Fin 4)), IsRefutation (PHP 5 4) π ∧ π.length ≤ 157 := by
  exact ⟨cert.map Prod.fst,
    ⟨chkR_sound _ (axPHP 5 4) (axPHP_sound 5 4) _ checked, by decide +kernel⟩,
    by decide +kernel⟩

end ProofComplexityBenchmark4

#print axioms ProofComplexityBenchmark4.exists_refutation
