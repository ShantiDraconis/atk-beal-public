import MCore.T26

namespace MCore

/-- General divisor-depth transport through exponentiation. -/
theorem T27_divisor_power_depth_scales
    {a d s n : Nat} (h : d ^ s ∣ a) :
    ∃ k : Nat, a ^ n = d ^ (s * n) * k := by
  rcases h with ⟨k, hk⟩
  refine ⟨k ^ n, ?_⟩
  calc
    a ^ n = ((d ^ s) * k) ^ n := congrArg (fun t : Nat => t ^ n) hk
    _ = (d ^ s) ^ n * k ^ n := T19_mul_pow (d ^ s) k n
    _ = d ^ (s * n) * k ^ n := by
      rw [T10_pow_mul_outer]

theorem T27_frey_a_divisor_depth
    {a b c x y z d s : Nat}
    (h : d ^ s ∣ a) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (d ^ (s * x) * k) ^ 2 *
          (b ^ y) ^ 2 * (c ^ z) ^ 2 := by
  rcases T27_divisor_power_depth_scales (a := a) (d := d) (s := s) (n := x) h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

theorem T27_frey_b_divisor_depth
    {a b c x y z d s : Nat}
    (h : d ^ s ∣ b) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 *
          (d ^ (s * y) * k) ^ 2 * (c ^ z) ^ 2 := by
  rcases T27_divisor_power_depth_scales (a := b) (d := d) (s := s) (n := y) h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

theorem T27_frey_c_divisor_depth
    {a b c x y z d s : Nat}
    (h : d ^ s ∣ c) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 *
          (d ^ (s * z) * k) ^ 2 := by
  rcases T27_divisor_power_depth_scales (a := c) (d := d) (s := s) (n := z) h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

def T27FreyDivisorDepthConstraint
    (a b c x y z : Nat) : Prop :=
  (∀ d s : Nat, d ^ s ∣ a →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (d ^ (s * x) * k) ^ 2 *
          (b ^ y) ^ 2 * (c ^ z) ^ 2) ∧
  (∀ d s : Nat, d ^ s ∣ b →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 *
          (d ^ (s * y) * k) ^ 2 * (c ^ z) ^ 2) ∧
  (∀ d s : Nat, d ^ s ∣ c →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 *
          (d ^ (s * z) * k) ^ 2)

def T27FreyDivisorDepthCandidate : Prop :=
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
    T20TwoAdicDepthConstraint a b c x y z ∧
    T21EqualExponentFactorConstraint a b c x y z ∧
    T22EqualOddExponentTwoAdicConstraint a b c x y z ∧
    T23EqualOddGapDepthConstraint a b c x y z ∧
    T24FreyDiscriminantConstraint a b c x y z ∧
    T25FreyTwoAdicDepthConstraint a b c x y z ∧
    T27FreyDivisorDepthConstraint a b c x y z

theorem T27_T25_to_frey_divisor_depth :
    T25FreyTwoAdicDepthCandidate → T27FreyDivisorDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, ?_⟩
  constructor
  · intro d s h
    exact T27_frey_a_divisor_depth h
  constructor
  · intro d s h
    exact T27_frey_b_divisor_depth h
  · intro d s h
    exact T27_frey_c_divisor_depth h

theorem T27_frey_divisor_depth_to_T25 :
    T27FreyDivisorDepthCandidate → T25FreyTwoAdicDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25⟩

theorem T27_candidate_iff_frey_divisor_depth :
    T25FreyTwoAdicDepthCandidate ↔ T27FreyDivisorDepthCandidate :=
  ⟨T27_T25_to_frey_divisor_depth, T27_frey_divisor_depth_to_T25⟩

def T27FreyDivisorDepthScientificFrontier : Prop :=
  ¬ T27FreyDivisorDepthCandidate

theorem T27_beal_iff_frey_divisor_depth_frontier :
    BealConjecture ↔ T27FreyDivisorDepthScientificFrontier := by
  rw [T25_beal_iff_frey_two_adic_depth_frontier]
  unfold T25FreyTwoAdicDepthScientificFrontier
    T27FreyDivisorDepthScientificFrontier
  exact not_congr T27_candidate_iff_frey_divisor_depth

#print axioms MCore.T27_divisor_power_depth_scales
#print axioms MCore.T27_frey_a_divisor_depth
#print axioms MCore.T27_frey_b_divisor_depth
#print axioms MCore.T27_frey_c_divisor_depth
#print axioms MCore.T27_candidate_iff_frey_divisor_depth
#print axioms MCore.T27_beal_iff_frey_divisor_depth_frontier

end MCore
