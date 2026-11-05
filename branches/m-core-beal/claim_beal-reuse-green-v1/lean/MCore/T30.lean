import MCore.T29

namespace MCore

/-- If a local prime divides a positive power, it divides the base. -/
theorem T30_prime_dvd_pow_succ
    {p a n : Nat} (hp : IsPrime p)
    (h : p ∣ a ^ (n + 1)) :
    p ∣ a := by
  induction n with
  | zero =>
      simpa using h
  | succ n ih =>
      have hmul : p ∣ a ^ (n + 1) * a := by
        simpa [Nat.pow_succ, Nat.succ_eq_add_one, Nat.add_assoc] using h
      rcases T29_prime_dvd_mul hp hmul with hprev | ha
      · exact ih hprev
      · exact ha

theorem T30_prime_dvd_pow_of_pos
    {p a n : Nat} (hp : IsPrime p) (hn : 0 < n)
    (h : p ∣ a ^ n) :
    p ∣ a := by
  cases n with
  | zero =>
      exact False.elim (Nat.not_lt_zero 0 hn)
  | succ n =>
      exact T30_prime_dvd_pow_succ hp (by simpa using h)

/-- Descend from the squared powered factor appearing in the Frey discriminant. -/
theorem T30_prime_dvd_power_square_to_base
    {p a n : Nat} (hp : IsPrime p) (hn : 0 < n)
    (h : p ∣ (a ^ n) ^ 2) :
    p ∣ a := by
  have hmul : p ∣ (a ^ n) * (a ^ n) := by
    simpa [Nat.pow_succ] using h
  rcases T29_prime_dvd_mul hp hmul with hpow | hpow
  · exact T30_prime_dvd_pow_of_pos hp hn hpow
  · exact T30_prime_dvd_pow_of_pos hp hn hpow

/-- Prime support of the Frey discriminant descends to the Beal bases,
    except for the explicit coefficient 16. -/
theorem T30_frey_base_prime_support
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : IsPrime p)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    p ∣ 16 ∨ p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  rcases T29_frey_prime_support hp hDelta with h16 | hA | hB | hC
  · exact Or.inl h16
  · exact Or.inr (Or.inl (T30_prime_dvd_power_square_to_base hp hx hA))
  · exact Or.inr (Or.inr (Or.inl (T30_prime_dvd_power_square_to_base hp hy hB)))
  · exact Or.inr (Or.inr (Or.inr (T30_prime_dvd_power_square_to_base hp hz hC)))

def T30FreyBasePrimeSupportConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat, IsPrime p →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
    p ∣ 16 ∨ p ∣ a ∨ p ∣ b ∨ p ∣ c

def T30FreyBasePrimeSupportCandidate : Prop :=
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
    T30FreyBasePrimeSupportConstraint a b c x y z

theorem T30_T28_to_base_prime_support :
    T28FreyPrimeSupportCandidate → T30FreyBasePrimeSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, h28⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, h28, ?_⟩
  intro p hp hDelta
  exact T30_frey_base_prime_support hx0 hy0 hz0 hp hDelta

theorem T30_base_prime_support_to_T28 :
    T30FreyBasePrimeSupportCandidate → T28FreyPrimeSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, h28, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, h24, h25, h27, h28⟩

theorem T30_candidate_iff_base_prime_support :
    T28FreyPrimeSupportCandidate ↔ T30FreyBasePrimeSupportCandidate :=
  ⟨T30_T28_to_base_prime_support, T30_base_prime_support_to_T28⟩

def T30FreyBasePrimeSupportScientificFrontier : Prop :=
  ¬ T30FreyBasePrimeSupportCandidate

theorem T30_beal_iff_base_prime_support_frontier :
    BealConjecture ↔ T30FreyBasePrimeSupportScientificFrontier := by
  rw [T28_beal_iff_prime_support_frontier]
  unfold T28FreyPrimeSupportScientificFrontier
    T30FreyBasePrimeSupportScientificFrontier
  exact not_congr T30_candidate_iff_base_prime_support

#print axioms MCore.T30_prime_dvd_pow_succ
#print axioms MCore.T30_prime_dvd_pow_of_pos
#print axioms MCore.T30_prime_dvd_power_square_to_base
#print axioms MCore.T30_frey_base_prime_support
#print axioms MCore.T30_candidate_iff_base_prime_support
#print axioms MCore.T30_beal_iff_base_prime_support_frontier

end MCore
