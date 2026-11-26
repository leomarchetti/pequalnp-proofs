import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17958

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
  PEqualNP.BlindGate PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

private def addAnd (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.and, [a, b]⟩], n + C.size⟩

private lemma wires_length (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  unfold Circuit.wires
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

private lemma extend (n : ℕ) (C : Circuit) (a b : ℕ) (hc : IsAO2 n C)
    (hn : ∀ g ∈ C.gates, g.inputs.Nodup) (hab : a ≠ b)
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (addAnd n C a b) ∧ (∀ g ∈ (addAnd n C a b).gates, g.inputs.Nodup) ∧
    ∀ x : Fin n → Bool, ∀ w < n + C.size,
      BlindGate.wireValue (addAnd n C a b) n x w = BlindGate.wireValue C n x w := by
  have appendGates : (addAnd n C a b).gates = C.gates ++ [⟨.and, [a,b]⟩] := rfl
  obtain ⟨hop, hback, harity⟩ := hc
  have hf (P : Gate → Prop) (hold : ∀ g ∈ C.gates, P g)
      (hnew : P ⟨.and, [a,b]⟩) : ∀ g ∈ (addAnd n C a b).gates, P g := by
    intro g hg
    simp only [appendGates, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hold g hg
    · exact hnew
  refine ⟨⟨hf _ hop (Or.inl rfl), ?_, hf _ harity rfl⟩, hf _ hn (by simp [hab]), ?_⟩
  · intro j hj i hi
    by_cases hlt : j < C.gates.length
    · unfold gateAt at hi
      rw [appendGates, List.getD_append _ _ _ _ hlt] at hi
      exact hback j hlt i hi
    · have he : j = C.gates.length := by
        simp [appendGates] at hj
        omega
      subst j
      unfold gateAt at hi
      rw [appendGates, List.getD_append_right _ _ _ _ (by rfl)] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro x w hw
    have hl : (C.wires (List.ofFn x)).length = n + C.size := by
      change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).length = n + C.gates.length
      rw [wires_length, List.length_ofFn]
    unfold BlindGate.wireValue Circuit.wires
    rw [appendGates, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    apply List.getD_append
    exact hl ▸ hw

end PEqualNP.Outside.L_meta_17958

theorem PEqualNP.Outside.L_meta_17958 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12) := by
  intro C a b hc hn hab ha hb
  obtain ⟨hmodel, hnodup, hwires⟩ := PEqualNP.Outside.L_meta_17958.extend 26 C a b hc hn hab ha hb
  refine ⟨PEqualNP.Outside.L_meta_17958.addAnd 26 C a b, C.size, ?_, hmodel, hnodup, rfl, ?_, hwires⟩
  · simp [PEqualNP.Outside.L_meta_17958.addAnd, PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [PEqualNP.Outside.L_meta_17958.addAnd, PEqualNP.CircuitLowerBounds.Circuit.size, List.getElem?_append_right]
