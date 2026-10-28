import MCore.T19

namespace MCore

/-- Full 2-adic depth scaling without introducing a valuation function:
    every factor 2^r in a base becomes a factor 2^(r*n) after the nth power. -/
theorem T20_two_power_depth_scales
    {a r n : Nat} (h : 2 ^ r ∣ a) :
    ∃ k : Nat, a ^ n = 2 ^ (r * n) * k := by
  rcases h with ⟨k, hk⟩
  refine ⟨k ^ n, ?_⟩
  calc
    a ^ n = ((2 ^ r) * k) ^ n := congrArg (fun t : Nat => t ^ n) hk
    _ = (2 ^ r) ^ n * k ^ n := T19_mul_pow (2 ^ r) k n
    _ = 2 ^ (r * n) * k ^ n := by
      rw [T10_pow_mul_outer]

theorem T20_a_depth_constraint
    {a b c x y z r : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (ha : 2 ^ r ∣ a) :
    ∃ k : Nat, c ^ z = 2 ^ (r * x) * k + b ^ y := by
  rcases T20_two_power_depth_scales (a := a) (r := r) (n := x) ha with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    c ^ z = a ^ x + b ^ y := heq.symm
    _ = 2 ^ (r * x) * k + b ^ y := congrArg (fun t : Nat => t + b ^ y) hk

theorem T20_b_depth_constraint
    {a b c x y z r : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hb : 2 ^ r ∣ b) :
    ∃ k : Nat, c ^ z = a ^ x + 2 ^ (r * y) * k := by
  rcases T20_two_power_depth_scales (a := b) (r := r) (n := y) hb with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    c ^ z = a ^ x + b ^ y := heq.symm
    _ = a ^ x + 2 ^ (r * y) * k := congrArg (fun t : Nat => a ^ x + t) hk

theorem T20_c_depth_constraint
    {a b c x y z r : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hc : 2 ^ r ∣ c) :
    ∃ k : Nat, a ^ x + b ^ y = 2 ^ (r * z) * k := by
  rcases T20_two_power_depth_scales (a := c) (r := r) (n := z) hc with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    a ^ x + b ^ y = c ^ z := heq
    _ = 2 ^ (r * z) * k := hk

def T20TwoAdicDepthConstraint (a b c x y z : Nat) : Prop :=
  (∀ r : Nat, 2 ^ r ∣ a →
    ∃ k : Nat, c ^ z = 2 ^ (r * x) * k + b ^ y) ∧
  (∀ r : Nat, 2 ^ r ∣ b →
    ∃ k : Nat, c ^ z = a ^ x + 2 ^ (r * y) * k) ∧
  (∀ r : Nat, 2 ^ r ∣ c →
    ∃ k : Nat, a ^ x + b ^ y = 2 ^ (r * z) * k)

def T20TwoAdicDepthCandidate : Prop :=
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
    T19VariableTwoAdicConstraint a b c x y z ∧
    T20TwoAdicDepthConstraint a b c x y z

theorem T20_T19_to_depth :
    T19VariableTwoAdicCandidate → T20TwoAdicDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19⟩
  refine ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, ?_⟩
  constructor
  · intro r har
    exact T20_a_depth_constraint heq har
  constructor
  · intro r hbr
    exact T20_b_depth_constraint heq hbr
  · intro r hcr
    exact T20_c_depth_constraint heq hcr

theorem T20_depth_to_T19 :
    T20TwoAdicDepthCandidate → T19VariableTwoAdicCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19⟩

theorem T20_candidate_iff_depth :
    T19VariableTwoAdicCandidate ↔ T20TwoAdicDepthCandidate :=
  ⟨T20_T19_to_depth, T20_depth_to_T19⟩

def T20TwoAdicDepthScientificFrontier : Prop :=
  ¬ T20TwoAdicDepthCandidate

theorem T20_beal_iff_two_adic_depth_frontier :
    BealConjecture ↔ T20TwoAdicDepthScientificFrontier := by
  rw [T19_beal_iff_variable_two_adic_frontier]
  unfold T19VariableTwoAdicScientificFrontier T20TwoAdicDepthScientificFrontier
  exact not_congr T20_candidate_iff_depth

#print axioms MCore.T20_two_power_depth_scales
#print axioms MCore.T20_a_depth_constraint
#print axioms MCore.T20_b_depth_constraint
#print axioms MCore.T20_c_depth_constraint
#print axioms MCore.T20_candidate_iff_depth
#print axioms MCore.T20_beal_iff_two_adic_depth_frontier

end MCore
