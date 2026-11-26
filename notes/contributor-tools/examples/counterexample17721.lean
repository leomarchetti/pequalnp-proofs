import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem counterexample : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) := by
  intro h
  let C : Circuit := ⟨[⟨GateOp.or, [0]⟩], 1⟩
  have hor : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    simp [C]
  have hinput : ∀ i : ℕ, ([true] : List Bool).getD i false = true →
      ([true, false] : List Bool).getD i false = true := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp at hi
  have hfalse : C.eval [true, false] = false := by decide
  have ht := h C hor [true] [true, false] hinput (by decide)
  rw [hfalse] at ht
  contradiction
