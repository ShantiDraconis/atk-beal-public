import MCore.T22

namespace MCore

/-- Transfer the full two-adic depth of an even A into the base gap C-B
    on the equal odd-exponent branch y=z. -/
theorem T23_a_even_equal_odd_gap_depth
    {a b c x y z s : Nat}
    (haPos : 0 < a)
    (hy : T7ReducedExponent y)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (haEven : T12Even a)
    (hyz : y = z)
    (hyne4 : y ≠ 4)
    (hs : 2 ^ s ∣ a) :
    2 ^ (s * x) ∣ c - b := by
  rcases T20_two_power_depth_scales (a := a) (r := s) (n := x) hs with ⟨k, hk⟩
  have hapow : 2 ^ (s * x) ∣ a ^ x := ⟨k, hk⟩
  have hexact :=
    T22_a_even_equal_odd_exponent_two_adic_exact
      (r := s * x) haPos hy heq hpar haEven hyz hyne4
  exact hexact.mp hapow

/-- Symmetric transfer for an even B on the equal odd-exponent branch x=z. -/
theorem T23_b_even_equal_odd_gap_depth
    {a b c x y z s : Nat}
    (hbPos : 0 < b)
    (hx : T7ReducedExponent x)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hbEven : T12Even b)
    (hxz : x = z)
    (hxne4 : x ≠ 4)
    (hs : 2 ^ s ∣ b) :
    2 ^ (s * y) ∣ c - a := by
  rcases T20_two_power_depth_scales (a := b) (r := s) (n := y) hs with ⟨k, hk⟩
  have hbpow : 2 ^ (s * y) ∣ b ^ y := ⟨k, hk⟩
  have hexact :=
    T22_b_even_equal_odd_exponent_two_adic_exact
      (r := s * y) hbPos hx heq hpar hbEven hxz hxne4
  exact hexact.mp hbpow

def T23EqualOddGapDepthConstraint (a b c x y z : Nat) : Prop :=
  (T12Even a → y = z → y ≠ 4 →
    ∀ s : Nat, 2 ^ s ∣ a → 2 ^ (s * x) ∣ c - b) ∧
  (T12Even b → x = z → x ≠ 4 →
    ∀ s : Nat, 2 ^ s ∣ b → 2 ^ (s * y) ∣ c - a)

def T23EqualOddGapDepthCandidate : Prop :=
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
    T23EqualOddGapDepthConstraint a b c x y z

theorem T23_T22_to_gap_depth :
    T22EqualOddExponentTwoAdicCandidate → T23EqualOddGapDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, ?_⟩
  constructor
  · intro hae hyz hyne4 s hs
    exact T23_a_even_equal_odd_gap_depth
      ha hy heq hpar hae hyz hyne4 hs
  · intro hbe hxz hxne4 s hs
    exact T23_b_even_equal_odd_gap_depth
      hb hx heq hpar hbe hxz hxne4 hs

theorem T23_gap_depth_to_T22 :
    T23EqualOddGapDepthCandidate → T22EqualOddExponentTwoAdicCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22⟩

theorem T23_candidate_iff_gap_depth :
    T22EqualOddExponentTwoAdicCandidate ↔ T23EqualOddGapDepthCandidate :=
  ⟨T23_T22_to_gap_depth, T23_gap_depth_to_T22⟩

def T23EqualOddGapDepthScientificFrontier : Prop :=
  ¬ T23EqualOddGapDepthCandidate

theorem T23_beal_iff_equal_odd_gap_depth_frontier :
    BealConjecture ↔ T23EqualOddGapDepthScientificFrontier := by
  rw [T22_beal_iff_equal_odd_exponent_two_adic_frontier]
  unfold T22EqualOddExponentTwoAdicScientificFrontier
    T23EqualOddGapDepthScientificFrontier
  exact not_congr T23_candidate_iff_gap_depth

#print axioms MCore.T23_a_even_equal_odd_gap_depth
#print axioms MCore.T23_b_even_equal_odd_gap_depth
#print axioms MCore.T23_candidate_iff_gap_depth
#print axioms MCore.T23_beal_iff_equal_odd_gap_depth_frontier

end MCore
