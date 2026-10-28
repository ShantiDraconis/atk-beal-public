import Init.Data.Nat.Gcd
import MCore.T26

namespace MCore

/-- Euclid's lemma for the repository-local elementary prime predicate,
    proved using the factor decomposition theorem Nat.dvd_mul available in
    Lean 4.19 core. -/
theorem T27_prime_dvd_mul
    {p m n : Nat} (hp : IsPrime p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n := by
  rcases (Nat.dvd_mul.mp h) with ⟨k1, k2, hk1m, hk2n, hkprod⟩
  have hk1p : k1 ∣ p := ⟨k2, hkprod.symm⟩
  rcases hp.2 k1 hk1p with hk1 | hk1
  · right
    have hk2p : k2 = p := by
      simpa [hk1] using hkprod
    rw [← hk2p]
    exact hk2n
  · left
    rw [← hk1]
    exact hk1m

/-- A local prime dividing a natural power already divides the base. -/
theorem T27_prime_dvd_pow
    {p a n : Nat} (hp : IsPrime p) (h : p ∣ a ^ n) :
    p ∣ a := by
  induction n with
  | zero =>
      have hp1 : p = 1 := Nat.eq_one_of_dvd_one (by simpa using h)
      exact False.elim ((Nat.ne_of_gt hp.1) hp1)
  | succ n ih =>
      rw [Nat.pow_succ] at h
      rcases T27_prime_dvd_mul hp h with hpow | ha
      · exact ih hpow
      · exact ha

/-- The only local prime divisor of the fixed factor 16 is 2. -/
theorem T27_prime_dvd_sixteen_eq_two
    {p : Nat} (hp : IsPrime p) (h16 : p ∣ 16) :
    p = 2 := by
  have hpow : p ∣ 2 ^ 4 := by
    simpa using h16
  have hp2 : p ∣ 2 :=
    T27_prime_dvd_pow hp hpow
  have hle : p ≤ 2 :=
    Nat.le_of_dvd (by decide : 0 < (2 : Nat)) hp2
  have hge : 2 ≤ p :=
    Nat.succ_le_of_lt hp.1
  exact Nat.le_antisymm hle hge

/-- Exact odd-prime support of the Frey discriminant. Any local prime p != 2
    dividing 16*A^(2x)*B^(2y)*C^(2z) divides at least one base A, B, C.

    This is a support theorem only: no minimal-discriminant or conductor
    exponent is asserted. -/
theorem T27_frey_odd_prime_support
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  unfold T24FreyDiscriminantBeal at hDelta
  rcases T27_prime_dvd_mul hp hDelta with hABC | hc2
  · rcases T27_prime_dvd_mul hp hABC with hAB | hb2
    · rcases T27_prime_dvd_mul hp hAB with h16 | ha2
      · exact False.elim (hp2 (T27_prime_dvd_sixteen_eq_two hp h16))
      · left
        have hax : p ∣ a ^ x :=
          T27_prime_dvd_pow hp ha2
        exact T27_prime_dvd_pow hp hax
    · right
      left
      have hby : p ∣ b ^ y :=
        T27_prime_dvd_pow hp hb2
      exact T27_prime_dvd_pow hp hby
  · right
    right
    have hcz : p ∣ c ^ z :=
      T27_prime_dvd_pow hp hc2
    exact T27_prime_dvd_pow hp hcz

def T27FreyOddPrimeSupportConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat, IsPrime p → p ≠ 2 →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
      p ∣ a ∨ p ∣ b ∨ p ∣ c

def T27FreyOddPrimeSupportCandidate : Prop :=
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
    T27FreyOddPrimeSupportConstraint a b c x y z

theorem T27_T25_to_odd_prime_support :
    T25FreyTwoAdicDepthCandidate → T27FreyOddPrimeSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, ?_⟩
  intro p hp hp2 hDelta
  exact T27_frey_odd_prime_support hp hp2 hDelta

theorem T27_odd_prime_support_to_T25 :
    T27FreyOddPrimeSupportCandidate → T25FreyTwoAdicDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25⟩

theorem T27_candidate_iff_odd_prime_support :
    T25FreyTwoAdicDepthCandidate ↔ T27FreyOddPrimeSupportCandidate :=
  ⟨T27_T25_to_odd_prime_support, T27_odd_prime_support_to_T25⟩

def T27FreyOddPrimeSupportScientificFrontier : Prop :=
  ¬ T27FreyOddPrimeSupportCandidate

theorem T27_beal_iff_odd_prime_support_frontier :
    BealConjecture ↔ T27FreyOddPrimeSupportScientificFrontier := by
  rw [T25_beal_iff_frey_two_adic_depth_frontier]
  unfold T25FreyTwoAdicDepthScientificFrontier
    T27FreyOddPrimeSupportScientificFrontier
  exact not_congr T27_candidate_iff_odd_prime_support

#print axioms MCore.T27_prime_dvd_mul
#print axioms MCore.T27_prime_dvd_pow
#print axioms MCore.T27_prime_dvd_sixteen_eq_two
#print axioms MCore.T27_frey_odd_prime_support
#print axioms MCore.T27_candidate_iff_odd_prime_support
#print axioms MCore.T27_beal_iff_odd_prime_support_frontier

end MCore
