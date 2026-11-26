import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18094

open PEqualNP.CircuitLowerBounds

/-- The witness circuit: gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_18094

theorem PEqualNP.Outside.L_meta_18094 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 9 ∧ (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun 5 (([0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)) x) ∧ (∀ j < C.size, C.output = 5 + j ∨ ∃ i < C.size, j < i ∧ 5 + j ∈ (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) :=
  by
    refine ⟨PEqualNP.Outside.L_meta_18094.witness, ?_, ?_, by decide⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_18094.witness]
    · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
      decide
