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


lemma kill (C : Circuit) (ho : ∀ g ∈ C.gates, g.op = GateOp.or) (N : ℕ)
    (x y z X1 X2 : List Bool) (hxl : x.length = N) (hy : y.length = N) (hz : z.length = N)
    (h1l : X1.length = N) (h2l : X2.length = N)
    (h : ∀ i < N, z.getD i false = (x.getD i false || y.getD i false))
    (hle1 : ∀ i < N, x.getD i false = true → X1.getD i false = true)
    (hle2 : ∀ i < N, y.getD i false = true → X2.getD i false = true)
    (hacc : C.eval z = true) (hr1 : C.eval X1 = false) (hr2 : C.eval X2 = false) : False := by
  have e := evalOr C ho x y z (by omega) (by omega) (by
    intro i
    rcases Nat.lt_or_ge i N with hi | hi
    · exact h i hi
    · rw [getD_past _ _ (by omega), getD_past _ _ (by omega), getD_past _ _ (by omega)]; rfl)
  rw [hacc] at e
  cases hx : C.eval x
  · rw [hx, Bool.false_or] at e
    have := evalMono C ho y X2 (by omega) (by
      intro i hi
      rcases Nat.lt_or_ge i N with hN | hN
      · exact hle2 i hN hi
      · rw [getD_past _ _ (by omega)] at hi; exact absurd hi (by simp)) e.symm
    rw [hr2] at this; exact absurd this (by simp)
  · have := evalMono C ho x X1 (by omega) (by
      intro i hi
      rcases Nat.lt_or_ge i N with hN | hN
      · exact hle1 i hN hi
      · rw [getD_past _ _ (by omega)] at hi; exact absurd hi (by simp)) hx
    rw [hr1] at this; exact absurd this (by simp)

end PEqualNP.Outside.Kit

set_option maxRecDepth 20000 in
theorem child_17601 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (13 : ℕ)),   x2 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]] →     x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →       have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Bool) =>         have x10 : List Bool := PEqualNP.GenericRejection.incidenceInput x7 x8;         x1.eval (x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false] ++ [x9]);       PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x1 → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → x7 {x10} {x11} (Decidable.decide (x10 = x3 ∧ x11 = x4)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → x7 x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size := by
  intro C x2 x3 x4 hx2 _ x7 hM hNo _ hacc hrej
  have onlyOr : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hAnd | hOr
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hNo ⟨⟨i, hi⟩, hAnd⟩).elim
    · exact hOr
  exfalso
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
  rcases hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 1] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([13, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 13] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
  · by_cases hb : ((0 : Fin 13) = x3 ∧ (4 : Fin 13) = x4)
    · obtain ⟨rfl, rfl⟩ := hb
      have ha := hacc 0 12 (by decide)
      simp only [x7] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,3,4,5} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({12} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,3,4,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,3,4,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simpa using ha) hr1 hr2
    · have ha := hacc 0 4 (by decide)
      simp only [x7, hb, decide_false] at ha hrej
      have hr1 := hrej {0,1,2,5} (by decide +kernel)
      have hr2 := hrej {1,2,3,6} (by decide +kernel)
      exact PEqualNP.Outside.Kit.kill C onlyOr 28 (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({4} : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({0,1,2,5} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({0,1,2,5} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false]) (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13)) ++ [([0, 14] : List ℕ).any fun (x8 : ℕ) => (PEqualNP.GenericRejection.incidenceInput ({1,2,3,6} : Finset (Fin 13)) ((PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 ({1,2,3,6} : Finset (Fin 13))) : Finset (Fin 13))).getD x8 Bool.false] ++ [Bool.false])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput])
        (by decide +kernel) (by decide +kernel) (by decide +kernel) ha hr1 hr2
