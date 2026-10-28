import MCore.T27

namespace MCore

/-- Exact local Euclid property missing from the current elementary IsPrime kernel. -/
def T28PrimeProductProperty : Prop :=
  ∀ p m n : Nat, IsPrime p → p ∣ m * n → p ∣ m ∨ p ∣ n

/-- Conditional prime-support split for the Frey discriminant.
    No claim is made here that T28PrimeProductProperty has already been proved. -/
theorem T28_frey_prime_support_of_product_property
    (hPP : T28PrimeProductProperty)
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    p ∣ 16 ∨
      p ∣ (a ^ x) ^ 2 ∨
      p ∣ (b ^ y) ^ 2 ∨
      p ∣ (c ^ z) ^ 2 := by
  unfold T24FreyDiscriminantBeal at hDelta
  rcases hPP p (16 * (a ^ x) ^ 2 * (b ^ y) ^ 2) ((c ^ z) ^ 2) hp hDelta with hABC | hC
  · rcases hPP p (16 * (a ^ x) ^ 2) ((b ^ y) ^ 2) hp hABC with hAB | hB
    · rcases hPP p 16 ((a ^ x) ^ 2) hp hAB with h16 | hA
      · exact Or.inl h16
      · exact Or.inr (Or.inl hA)
    · exact Or.inr (Or.inr (Or.inl hB))
  · exact Or.inr (Or.inr (Or.inr hC))

/-- T28 stores the exact conditional support theorem. -/
def T28FreyPrimeSupportConstraint
    (a b c x y z : Nat) : Prop :=
  T28PrimeProductProperty →
    ∀ p : Nat, IsPrime p →
      p ∣ T24FreyDiscriminantBeal a b c x y z →
      p ∣ 16 ∨
        p ∣ (a ^ x) ^ 2 ∨
        p ∣ (b ^ y) ^ 2 ∨
        p ∣ (c ^ z) ^ 2

def T28FreyPrimeSupportCandidate : Prop :=
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
    T28FreyPrimeSupportConstraint a b c x y z

theorem T28_T27_to_prime_support :
    T27FreyDivisorDepthCandidate → T28FreyPrimeSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, ?_⟩
  intro hPP p hp hDelta
  exact T28_frey_prime_support_of_product_property hPP hp hDelta

theorem T28_prime_support_to_T27 :
    T28FreyPrimeSupportCandidate → T27FreyDivisorDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27⟩

theorem T28_candidate_iff_prime_support :
    T27FreyDivisorDepthCandidate ↔ T28FreyPrimeSupportCandidate :=
  ⟨T28_T27_to_prime_support, T28_prime_support_to_T27⟩

def T28FreyPrimeSupportScientificFrontier : Prop :=
  ¬ T28FreyPrimeSupportCandidate

theorem T28_beal_iff_prime_support_frontier :
    BealConjecture ↔ T28FreyPrimeSupportScientificFrontier := by
  rw [T27_beal_iff_frey_divisor_depth_frontier]
  unfold T27FreyDivisorDepthScientificFrontier
    T28FreyPrimeSupportScientificFrontier
  exact not_congr T28_candidate_iff_prime_support

#print axioms MCore.T28_frey_prime_support_of_product_property
#print axioms MCore.T28_candidate_iff_prime_support
#print axioms MCore.T28_beal_iff_prime_support_frontier

end MCore
