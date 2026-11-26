import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25232.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.and, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25232.Helpers

theorem PEqualNP.Outside.L_meta_25232 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50097 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25232.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25232.Helpers.witness]
