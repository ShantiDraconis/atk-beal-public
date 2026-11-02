namespace MCore.K9.Core

/-- Right-successor form of addition, reduced by the Nat kernel equations. -/
theorem add_succ_core (a b : Nat) : a + (b + 1) = (a + b) + 1 := rfl

/-- Right-successor form of multiplication, reduced by the Nat kernel equations. -/
theorem mul_succ_core (a b : Nat) : a * (b + 1) = a * b + a := rfl

/-- Local associativity of addition, avoiding the library theorem Nat.add_assoc. -/
theorem add_assoc_core (a b c : Nat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c ih => exact congrArg Nat.succ ih

/-- Local right-distributivity needed for multiplication associativity. -/
theorem mul_add_core (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [add_succ_core, mul_succ_core, ih, mul_succ_core, add_assoc_core]

/-- Local multiplication associativity for the K9 zero-axiom firewall. -/
theorem mul_assoc_core (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [mul_succ_core, ih, mul_succ_core, mul_add_core]

end MCore.K9.Core
