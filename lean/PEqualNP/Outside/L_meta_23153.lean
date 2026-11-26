import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23153.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [3, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_23153.Helpers

theorem PEqualNP.Outside.L_meta_23153 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30457 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23153.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23153.Helpers.witness]
