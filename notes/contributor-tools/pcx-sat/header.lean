import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.NSNAME

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

-- Res(lin): the assignment check of a weakening runs over the variables vs only
def ext {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (b : Bool) : V → Bool :=
  fun w => if w = v then b else a w

def allA {V : Type} [DecidableEq V] : List V → List (V → Bool)
  | [] => [fun _ => false]
  | v :: vs => (allA vs).flatMap (fun a => [ext a v false, ext a v true])

theorem allA_cover {V : Type} [DecidableEq V] :
    ∀ (vs : List V) (a : V → Bool), ∃ b ∈ allA vs, ∀ v ∈ vs, b v = a v
  | [], a => ⟨fun _ => false, by simp [allA], by simp⟩
  | v :: vs, a => by
    obtain ⟨b, hb, hba⟩ := allA_cover vs a
    refine ⟨ext b v (a v), ?_, ?_⟩
    · simp only [allA, List.mem_flatMap]
      exact ⟨b, hb, by cases a v <;> simp⟩
    · intro w hw
      simp only [ext]
      split_ifs with hwv
      · rw [hwv]
      · exact hba w (by simpa [hwv] using hw)

def satB {V : Type} (a : V → Bool) (C : LinClause V) : Bool :=
  decide (∃ q ∈ C, decide (Odd (q.1.filter (fun v => a v = true)).card) = q.2)

theorem satB_iff {V : Type} (a : V → Bool) (C : LinClause V) :
    satB a C = true ↔ LinClauseSat a C := by
  unfold satB LinClauseSat LinEqSat
  simp only [decide_eq_true_eq]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rcases q with ⟨f, b⟩
  cases b <;> simp

theorem sat_congr {V : Type} (a b : V → Bool) (C : LinClause V) (vs : List V)
    (hv : ∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) (hab : ∀ v ∈ vs, b v = a v) :
    LinClauseSat b C ↔ LinClauseSat a C := by
  unfold LinClauseSat LinEqSat
  refine exists_congr fun q => and_congr_right fun hq => ?_
  rw [Finset.filter_congr (fun v hv' => by rw [hab v (hv q hq v hv')])]

def wkB {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V) : Bool :=
  decide (∀ q ∈ C, ∀ v ∈ q.1, v ∈ vs) && decide (∀ q ∈ D, ∀ v ∈ q.1, v ∈ vs) &&
    (allA vs).all (fun a => !satB a C || satB a D)

theorem wkB_sound {V : Type} [DecidableEq V] (vs : List V) (C D : LinClause V)
    (h : wkB vs C D = true) : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D := by
  simp only [wkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hC, hD⟩, hall⟩ := h
  intro a ha
  obtain ⟨b, hb, hba⟩ := allA_cover vs a
  have hh := hall b hb
  rw [← sat_congr a b D vs hD hba]
  rw [← sat_congr a b C vs hC hba, ← satB_iff] at ha
  rw [← satB_iff]
  simpa [ha] using hh

inductive Step (V : Type) where
  | ax : Clause V → Step V
  | rs : ℕ → ℕ → Finset V → Step V
  | wk : ℕ → List V → Step V

def chkL {V : Type} [DecidableEq V] (ax : Clause V → Bool) :
    List (LinClause V × Step V) → Bool
  | [] => true
  | (R, .ax C) :: t => ax C && decide (linOfClause C = R) && chkL ax t
  | (R, .rs i j f) :: t =>
      decide (i < t.length) && decide (j < t.length) &&
      decide ((f, false) ∈ (t.map Prod.fst).getD i ∅ ∧ (f, true) ∈ (t.map Prod.fst).getD j ∅ ∧
        R = ((t.map Prod.fst).getD i ∅).erase (f, false) ∪ ((t.map Prod.fst).getD j ∅).erase (f, true)) &&
      chkL ax t
  | (R, .wk i vs) :: t => decide (i < t.length) && wkB vs ((t.map Prod.fst).getD i ∅) R && chkL ax t

theorem chkL_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (ax : Clause V → Bool)
    (hax : ∀ C, ax C = true → C ∈ F) :
    ∀ l, chkL ax l = true → IsLinDerivation ((fun C => linOfClause C) '' F) (l.map Prod.fst)
  | [], _ => IsLinDerivation.nil
  | (R, .ax C) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, ht⟩ := h
    exact IsLinDerivation.ax (chkL_sound F ax hax t ht) ⟨C, hax C h1, h2⟩
  | (R, .rs i j f) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, h1, h2, h3⟩, ht⟩ := h
    exact IsLinDerivation.res (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (memD _ _ _ (by simpa using hj)) ⟨f, h1, h2, h3⟩
  | (R, .wk i vs) :: t, h => by
    simp only [chkL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h1⟩, ht⟩ := h
    exact IsLinDerivation.weak (chkL_sound F ax hax t ht) (memD _ _ _ (by simpa using hi))
      (wkB_sound vs _ R h1)

def axPHP (m n : ℕ) (C : Clause (Fin m × Fin n)) : Bool :=
  decide (∃ i : Fin m, C = Finset.univ.image (fun j : Fin n => ((i, j), true))) ||
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ j : Fin n, i ≠ i' ∧ C = {((i, j), false), ((i', j), false)})

theorem axPHP_sound (m n : ℕ) : ∀ C, axPHP m n C = true → C ∈ PHP m n := by
  intro C h
  simp only [axPHP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨i, hi⟩ | ⟨i, i', j, hne, hC⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨i, i', j, hne, hC⟩

def bitF (c0 c1 : Bool) : Fin 2 → Bool := fun b => if b.val = 0 then c0 else c1

def axBPHP (m : ℕ) (C : Clause (Fin m × Fin 2)) : Bool :=
  decide (∃ i : Fin m, ∃ i' : Fin m, ∃ c0 : Bool, ∃ c1 : Bool, i ≠ i' ∧
    C = Finset.univ.image (fun b : Fin 2 => ((i, b), !bitF c0 c1 b)) ∪
        Finset.univ.image (fun b : Fin 2 => ((i', b), !bitF c0 c1 b)))

theorem axBPHP_sound (m : ℕ) : ∀ C, axBPHP m C = true → C ∈ BPHP m 2 := by
  intro C h
  simp only [axBPHP, decide_eq_true_eq] at h
  obtain ⟨i, i', c0, c1, hne, hC⟩ := h
  exact ⟨i, i', bitF c0 c1, hne, hC⟩

