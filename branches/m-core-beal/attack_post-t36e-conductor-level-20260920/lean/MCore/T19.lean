import MCore.T18

namespace MCore

/-- Elementary multiplicativity of powers, kept local to avoid adding an
    external algebra dependency to the 2-adic layer. -/
theorem T19_mul_pow (a b n : Nat) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- If a base is even, its nth power contains the full factor 2^n. -/
theorem T19_even_power_factor
    {a n : Nat} (ha : T12Even a) :
    ∃ k : Nat, a ^ n = 2 ^ n * k := by
  rcases ha with ⟨k, hk⟩
  refine ⟨k ^ n, ?_⟩
  calc
    a ^ n = (2 * k) ^ n := congrArg (fun t : Nat => t ^ n) hk
    _ = 2 ^ n * k ^ n := T19_mul_pow 2 k n

/-- If A is the unique even base, the equation is congruent modulo the
    variable modulus 2^x, not merely modulo a fixed small power of two. -/
theorem T19_a_even_variable_two_adic
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (ha : T12Even a) :
    ∃ k : Nat, c ^ z = 2 ^ x * k + b ^ y := by
  rcases T19_even_power_factor (a := a) (n := x) ha with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    c ^ z = a ^ x + b ^ y := heq.symm
    _ = 2 ^ x * k + b ^ y := congrArg (fun t : Nat => t + b ^ y) hk

/-- Symmetric variable 2-adic lift for an even B. -/
theorem T19_b_even_variable_two_adic
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hb : T12Even b) :
    ∃ k : Nat, c ^ z = a ^ x + 2 ^ y * k := by
  rcases T19_even_power_factor (a := b) (n := y) hb with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    c ^ z = a ^ x + b ^ y := heq.symm
    _ = a ^ x + 2 ^ y * k := congrArg (fun t : Nat => a ^ x + t) hk

/-- If C is the unique even base, the entire left-hand side contains the
    variable factor 2^z. -/
theorem T19_c_even_variable_two_adic
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hc : T12Even c) :
    ∃ k : Nat, a ^ x + b ^ y = 2 ^ z * k := by
  rcases T19_even_power_factor (a := c) (n := z) hc with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    a ^ x + b ^ y = c ^ z := heq
    _ = 2 ^ z * k := hk

def T19VariableTwoAdicConstraint (a b c x y z : Nat) : Prop :=
  (T12Even a → ∃ k : Nat, c ^ z = 2 ^ x * k + b ^ y) ∧
  (T12Even b → ∃ k : Nat, c ^ z = a ^ x + 2 ^ y * k) ∧
  (T12Even c → ∃ k : Nat, a ^ x + b ^ y = 2 ^ z * k)

def T19VariableTwoAdicCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c ∧
    T12ExactlyOneEven a b c ∧
    (T12Even c → ¬ (x = 4 ∧ y = 4)) ∧
    T14CResidueConstraint a b c x y z ∧
    T15CBaseResidueConstraint a b c x y z ∧
    T16CEightConstraint a b c x y z ∧
    T17CEvenClassifier a b c x y z ∧
    T18AEvenClassifier a b c x y z ∧
    T18BEvenClassifier a b c x y z ∧
    T19VariableTwoAdicConstraint a b c x y z

theorem T19_T18_to_variable_two_adic :
    T18FullParityClassifiedCandidate → T19VariableTwoAdicCandidate := by
  rintro ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b⟩
  refine ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, ?_⟩
  constructor
  · intro hae
    exact T19_a_even_variable_two_adic heq hae
  constructor
  · intro hbe
    exact T19_b_even_variable_two_adic heq hbe
  · intro hce
    exact T19_c_even_variable_two_adic heq hce

theorem T19_variable_two_adic_to_T18 :
    T19VariableTwoAdicCandidate → T18FullParityClassifiedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b⟩

theorem T19_candidate_iff_variable_two_adic :
    T18FullParityClassifiedCandidate ↔ T19VariableTwoAdicCandidate :=
  ⟨T19_T18_to_variable_two_adic, T19_variable_two_adic_to_T18⟩

def T19VariableTwoAdicScientificFrontier : Prop :=
  ¬ T19VariableTwoAdicCandidate

theorem T19_beal_iff_variable_two_adic_frontier :
    BealConjecture ↔ T19VariableTwoAdicScientificFrontier := by
  rw [T18_beal_iff_full_parity_frontier]
  unfold T18FullParityScientificFrontier T19VariableTwoAdicScientificFrontier
  exact not_congr T19_candidate_iff_variable_two_adic

#print axioms MCore.T19_mul_pow
#print axioms MCore.T19_even_power_factor
#print axioms MCore.T19_a_even_variable_two_adic
#print axioms MCore.T19_b_even_variable_two_adic
#print axioms MCore.T19_c_even_variable_two_adic
#print axioms MCore.T19_candidate_iff_variable_two_adic
#print axioms MCore.T19_beal_iff_variable_two_adic_frontier

end MCore
