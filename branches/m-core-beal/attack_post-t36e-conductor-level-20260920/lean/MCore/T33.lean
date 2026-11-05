import MCore.T32

namespace MCore

/-- Exact arithmetic package available at an odd prime of the Frey
    discriminant after T31-T32.  This deliberately contains no semantic claim
    about Kodaira type, minimality, or conductor. -/
def T33OddPrimeReductionInput
    (a b c x y z p : Nat) : Prop :=
  IsPrime p ∧
  p ≠ 2 ∧
  p ∣ T24FreyDiscriminantBeal a b c x y z ∧
  ¬ p ∣ T32FreyC4Kernel a b x y ∧
  (p ∣ a ∨ p ∣ b ∨ p ∣ c)

/-- Every odd prime divisor of the Frey discriminant carries the complete
    arithmetic input package proved so far. -/
theorem T33_odd_delta_prime_has_reduction_input
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hp : IsPrime p) (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    T33OddPrimeReductionInput a b c x y z p := by
  refine ⟨hp, hp2, hDelta, ?_, ?_⟩
  · exact T32_no_odd_common_prime_delta_c4
      hx hy hz heq hpw hp hp2 hDelta
  · rcases T31_frey_radical_prime_support hx hy hz hp hDelta with hpEq | ha | hb | hc
    · exact False.elim (hp2 hpEq)
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hc)

/-- A generic contract for any future formal local-reduction theory.
    The predicate [ReductionAt] is supplied by that future theory; T33 does not
    manufacture or assume one. -/
def T33LocalReductionContract
    (ReductionAt : Nat → Prop)
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat,
    T33OddPrimeReductionInput a b c x y z p →
    ReductionAt p

/-- The direct odd-discriminant-prime goal for the same external predicate. -/
def T33OddDeltaReductionGoal
    (ReductionAt : Nat → Prop)
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat,
    IsPrime p →
    p ≠ 2 →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
    ReductionAt p

/-- Under the arithmetic hypotheses already certified, the external local
    reduction goal is equivalent to providing a reduction theorem exactly on
    the T33 input package.  This pins the remaining bridge without asserting
    it. -/
theorem T33_reduction_goal_iff_local_contract
    {a b c x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (ReductionAt : Nat → Prop) :
    T33OddDeltaReductionGoal ReductionAt a b c x y z ↔
      T33LocalReductionContract ReductionAt a b c x y z := by
  constructor
  · intro hGoal p hInput
    exact hGoal p hInput.1 hInput.2.1 hInput.2.2.1
  · intro hContract p hp hp2 hDelta
    apply hContract p
    exact T33_odd_delta_prime_has_reduction_input
      hx hy hz heq hpw hp hp2 hDelta

def T33OddPrimeReductionInputConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat,
    IsPrime p →
    p ≠ 2 →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
    T33OddPrimeReductionInput a b c x y z p

def T33OddPrimeReductionInputCandidate : Prop :=
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
    T27FreyDivisorDepthConstraint a b c x y z ∧
    T28FreyPrimeSupportConstraint a b c x y z ∧
    T30FreyBasePrimeSupportConstraint a b c x y z ∧
    T31FreyRadicalSupportConstraint a b c x y z ∧
    T32FreyC4CoprimeConstraint a b c x y z ∧
    T33OddPrimeReductionInputConstraint a b c x y z

theorem T33_T32_to_reduction_input :
    T32FreyC4CoprimeCandidate → T33OddPrimeReductionInputCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, ?_⟩
  intro p hp hp2 hDelta
  exact T33_odd_delta_prime_has_reduction_input
    hx0 hy0 hz0 heq hpw hp hp2 hDelta

theorem T33_reduction_input_to_T32 :
    T33OddPrimeReductionInputCandidate → T32FreyC4CoprimeCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32⟩

theorem T33_candidate_iff_reduction_input :
    T32FreyC4CoprimeCandidate ↔ T33OddPrimeReductionInputCandidate :=
  ⟨T33_T32_to_reduction_input, T33_reduction_input_to_T32⟩

def T33OddPrimeReductionInputScientificFrontier : Prop :=
  ¬ T33OddPrimeReductionInputCandidate

theorem T33_beal_iff_reduction_input_frontier :
    BealConjecture ↔ T33OddPrimeReductionInputScientificFrontier := by
  rw [T32_beal_iff_c4_coprime_frontier]
  unfold T32FreyC4CoprimeScientificFrontier
    T33OddPrimeReductionInputScientificFrontier
  exact not_congr T33_candidate_iff_reduction_input

#print axioms MCore.T33_odd_delta_prime_has_reduction_input
#print axioms MCore.T33_reduction_goal_iff_local_contract
#print axioms MCore.T33_candidate_iff_reduction_input
#print axioms MCore.T33_beal_iff_reduction_input_frontier

end MCore
