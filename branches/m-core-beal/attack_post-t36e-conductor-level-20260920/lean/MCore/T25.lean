import MCore.T24

namespace MCore

/-- Exact transport of 2-adic base depth into the A-factor of the Frey
    discriminant. No valuation, minimal model, conductor, or modularity claim
    is introduced here. -/
theorem T25_frey_a_two_adic_factorization
    {a b c x y z s : Nat}
    (hs : 2 ^ s ∣ a) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (2 ^ (s * x) * k) ^ 2 *
          (b ^ y) ^ 2 * (c ^ z) ^ 2 := by
  rcases T20_two_power_depth_scales (a := a) (r := s) (n := x) hs with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

/-- Symmetric B-factor transport. -/
theorem T25_frey_b_two_adic_factorization
    {a b c x y z s : Nat}
    (hs : 2 ^ s ∣ b) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 *
          (2 ^ (s * y) * k) ^ 2 * (c ^ z) ^ 2 := by
  rcases T20_two_power_depth_scales (a := b) (r := s) (n := y) hs with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

/-- Symmetric C-factor transport. -/
theorem T25_frey_c_two_adic_factorization
    {a b c x y z s : Nat}
    (hs : 2 ^ s ∣ c) :
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 *
          (2 ^ (s * z) * k) ^ 2 := by
  rcases T20_two_power_depth_scales (a := c) (r := s) (n := z) hs with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold T24FreyDiscriminantBeal
  rw [hk]

/-- T25 stores only exact factorization data forced by the already-proved
    power-depth lemma T20. -/
def T25FreyTwoAdicDepthConstraint
    (a b c x y z : Nat) : Prop :=
  (∀ s : Nat, 2 ^ s ∣ a →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (2 ^ (s * x) * k) ^ 2 *
          (b ^ y) ^ 2 * (c ^ z) ^ 2) ∧
  (∀ s : Nat, 2 ^ s ∣ b →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 *
          (2 ^ (s * y) * k) ^ 2 * (c ^ z) ^ 2) ∧
  (∀ s : Nat, 2 ^ s ∣ c →
    ∃ k : Nat,
      T24FreyDiscriminantBeal a b c x y z =
        16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 *
          (2 ^ (s * z) * k) ^ 2)

def T25FreyTwoAdicDepthCandidate : Prop :=
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
    T25FreyTwoAdicDepthConstraint a b c x y z

theorem T25_T24_to_frey_two_adic_depth :
    T24FreyDiscriminantCandidate → T25FreyTwoAdicDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, ?_⟩
  constructor
  · intro s hs
    exact T25_frey_a_two_adic_factorization hs
  constructor
  · intro s hs
    exact T25_frey_b_two_adic_factorization hs
  · intro s hs
    exact T25_frey_c_two_adic_factorization hs

theorem T25_frey_two_adic_depth_to_T24 :
    T25FreyTwoAdicDepthCandidate → T24FreyDiscriminantCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24⟩

theorem T25_candidate_iff_frey_two_adic_depth :
    T24FreyDiscriminantCandidate ↔ T25FreyTwoAdicDepthCandidate :=
  ⟨T25_T24_to_frey_two_adic_depth, T25_frey_two_adic_depth_to_T24⟩

def T25FreyTwoAdicDepthScientificFrontier : Prop :=
  ¬ T25FreyTwoAdicDepthCandidate

theorem T25_beal_iff_frey_two_adic_depth_frontier :
    BealConjecture ↔ T25FreyTwoAdicDepthScientificFrontier := by
  rw [T24_beal_iff_frey_discriminant_frontier]
  unfold T24FreyDiscriminantScientificFrontier
    T25FreyTwoAdicDepthScientificFrontier
  exact not_congr T25_candidate_iff_frey_two_adic_depth

#print axioms MCore.T25_frey_a_two_adic_factorization
#print axioms MCore.T25_frey_b_two_adic_factorization
#print axioms MCore.T25_frey_c_two_adic_factorization
#print axioms MCore.T25_candidate_iff_frey_two_adic_depth
#print axioms MCore.T25_beal_iff_frey_two_adic_depth_frontier

end MCore
