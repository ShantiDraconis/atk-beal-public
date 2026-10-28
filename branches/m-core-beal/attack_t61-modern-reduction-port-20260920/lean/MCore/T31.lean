import MCore.T30

namespace MCore

/-- A local prime divisor of 2 is exactly 2. -/
theorem T31_prime_dvd_two_eq_two
    {p : Nat} (hp : IsPrime p) (h : p ∣ 2) :
    p = 2 := by
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  have hge : 2 ≤ p := Nat.succ_le_of_lt hp.1
  exact Nat.le_antisymm hle hge

/-- The only local prime divisor of the explicit Frey coefficient 16 is 2. -/
theorem T31_prime_dvd_sixteen_eq_two
    {p : Nat} (hp : IsPrime p) (h : p ∣ 16) :
    p = 2 := by
  have h16 : p ∣ 2 * 8 := by simpa using h
  rcases T29_prime_dvd_mul hp h16 with h2 | h8
  · exact T31_prime_dvd_two_eq_two hp h2
  · have h8' : p ∣ 2 * 4 := by simpa using h8
    rcases T29_prime_dvd_mul hp h8' with h2 | h4
    · exact T31_prime_dvd_two_eq_two hp h2
    · have h4' : p ∣ 2 * 2 := by simpa using h4
      rcases T29_prime_dvd_mul hp h4' with h2 | h2
      · exact T31_prime_dvd_two_eq_two hp h2
      · exact T31_prime_dvd_two_eq_two hp h2

/-- Exact prime support of the integral Frey discriminant:
    every prime divisor is 2 or divides one of the Beal bases.
    This is a support statement only; it is not a conductor/minimality claim. -/
theorem T31_frey_radical_prime_support
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : IsPrime p)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    p = 2 ∨ p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  rcases T30_frey_base_prime_support hx hy hz hp hDelta with h16 | ha | hb | hc
  · exact Or.inl (T31_prime_dvd_sixteen_eq_two hp h16)
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr hc))

def T31FreyRadicalSupportConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat, IsPrime p →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
    p = 2 ∨ p ∣ a ∨ p ∣ b ∨ p ∣ c

def T31FreyRadicalSupportCandidate : Prop :=
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
    T31FreyRadicalSupportConstraint a b c x y z

theorem T31_T30_to_radical_support :
    T30FreyBasePrimeSupportCandidate → T31FreyRadicalSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, ?_⟩
  intro p hp hDelta
  exact T31_frey_radical_prime_support hx0 hy0 hz0 hp hDelta

theorem T31_radical_support_to_T30 :
    T31FreyRadicalSupportCandidate → T30FreyBasePrimeSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30⟩

theorem T31_candidate_iff_radical_support :
    T30FreyBasePrimeSupportCandidate ↔ T31FreyRadicalSupportCandidate :=
  ⟨T31_T30_to_radical_support, T31_radical_support_to_T30⟩

def T31FreyRadicalSupportScientificFrontier : Prop :=
  ¬ T31FreyRadicalSupportCandidate

theorem T31_beal_iff_radical_support_frontier :
    BealConjecture ↔ T31FreyRadicalSupportScientificFrontier := by
  rw [T30_beal_iff_base_prime_support_frontier]
  unfold T30FreyBasePrimeSupportScientificFrontier
    T31FreyRadicalSupportScientificFrontier
  exact not_congr T31_candidate_iff_radical_support

#print axioms MCore.T31_prime_dvd_two_eq_two
#print axioms MCore.T31_prime_dvd_sixteen_eq_two
#print axioms MCore.T31_frey_radical_prime_support
#print axioms MCore.T31_candidate_iff_radical_support
#print axioms MCore.T31_beal_iff_radical_support_frontier

end MCore
