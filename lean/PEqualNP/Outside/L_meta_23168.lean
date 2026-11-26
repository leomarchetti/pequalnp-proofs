import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23168.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [3, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_23168.Helpers

theorem PEqualNP.Outside.L_meta_23168 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23168.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23168.Helpers.witness]
