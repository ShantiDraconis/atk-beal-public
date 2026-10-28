import MCore.T27

namespace MCore

/-- If a prime divides A, then it divides the Frey discriminant. -/
theorem T28_prime_of_a_divides_frey_discriminant
    {a b c x y z p : Nat}
    (hx : 0 < x)
    (hpa : p ∣ a) :
    p ∣ T24FreyDiscriminantBeal a b c x y z := by
  have hax : p ∣ a ^ x := T11_dvd_pow_of_dvd hx hpa
  have ha2 : p ∣ (a ^ x) ^ 2 :=
    T11_dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hax
  unfold T24FreyDiscriminantBeal
  have h1 : p ∣ 16 * (a ^ x) ^ 2 :=
    Nat.dvd_mul_left_of_dvd ha2 16
  have h2 : p ∣ (16 * (a ^ x) ^ 2) * (b ^ y) ^ 2 :=
    Nat.dvd_mul_right_of_dvd h1 ((b ^ y) ^ 2)
  exact Nat.dvd_mul_right_of_dvd h2 ((c ^ z) ^ 2)

/-- Symmetric B-support inclusion. -/
theorem T28_prime_of_b_divides_frey_discriminant
    {a b c x y z p : Nat}
    (hy : 0 < y)
    (hpb : p ∣ b) :
    p ∣ T24FreyDiscriminantBeal a b c x y z := by
  have hby : p ∣ b ^ y := T11_dvd_pow_of_dvd hy hpb
  have hb2 : p ∣ (b ^ y) ^ 2 :=
    T11_dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hby
  unfold T24FreyDiscriminantBeal
  have h1 : p ∣ (16 * (a ^ x) ^ 2) * (b ^ y) ^ 2 :=
    Nat.dvd_mul_left_of_dvd hb2 (16 * (a ^ x) ^ 2)
  exact Nat.dvd_mul_right_of_dvd h1 ((c ^ z) ^ 2)

/-- Symmetric C-support inclusion. -/
theorem T28_prime_of_c_divides_frey_discriminant
    {a b c x y z p : Nat}
    (hz : 0 < z)
    (hpc : p ∣ c) :
    p ∣ T24FreyDiscriminantBeal a b c x y z := by
  have hcz : p ∣ c ^ z := T11_dvd_pow_of_dvd hz hpc
  have hc2 : p ∣ (c ^ z) ^ 2 :=
    T11_dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hcz
  unfold T24FreyDiscriminantBeal
  exact Nat.dvd_mul_left_of_dvd hc2
    ((16 * (a ^ x) ^ 2) * (b ^ y) ^ 2)

/-- For an odd local prime, support in the Frey discriminant is exactly
    support in one of the three Beal bases. -/
theorem T28_frey_odd_prime_support_iff
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    p ∣ T24FreyDiscriminantBeal a b c x y z ↔
      p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  constructor
  · intro hDelta
    exact T27_frey_odd_prime_support hp hp2 hDelta
  · intro h
    rcases h with hpa | hpb | hpc
    · exact T28_prime_of_a_divides_frey_discriminant hx hpa
    · exact T28_prime_of_b_divides_frey_discriminant hy hpb
    · exact T28_prime_of_c_divides_frey_discriminant hz hpc

/-- Pairwise primitiveness makes the odd-prime base support exclusive:
    no local prime can divide two distinct bases. -/
theorem T28_pairwise_prime_exclusive
    {a b c p : Nat}
    (hp : IsPrime p)
    (hpw : T11PairwisePrimitive a b c) :
    (¬ (p ∣ a ∧ p ∣ b)) ∧
    (¬ (p ∣ a ∧ p ∣ c)) ∧
    (¬ (p ∣ b ∧ p ∣ c)) := by
  constructor
  · rintro ⟨hpa, hpb⟩
    exact hpw.1 ⟨p, hp.1, hpa, hpb⟩
  constructor
  · rintro ⟨hpa, hpc⟩
    exact hpw.2.1 ⟨p, hp.1, hpa, hpc⟩
  · rintro ⟨hpb, hpc⟩
    exact hpw.2.2 ⟨p, hp.1, hpb, hpc⟩

def T28ExactlyOneBaseSupport (p a b c : Nat) : Prop :=
  (p ∣ a ∧ ¬ p ∣ b ∧ ¬ p ∣ c) ∨
  (¬ p ∣ a ∧ p ∣ b ∧ ¬ p ∣ c) ∨
  (¬ p ∣ a ∧ ¬ p ∣ b ∧ p ∣ c)

/-- Every odd prime in the discriminant of a pairwise-primitive candidate
    belongs to exactly one base. -/
theorem T28_frey_odd_prime_exactly_one_base
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hpw : T11PairwisePrimitive a b c)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    T28ExactlyOneBaseSupport p a b c := by
  have hsupp : p ∣ a ∨ p ∣ b ∨ p ∣ c :=
    (T28_frey_odd_prime_support_iff hp hp2 hx hy hz).mp hDelta
  have hex := T28_pairwise_prime_exclusive hp hpw
  rcases hsupp with hpa | hpb | hpc
  · left
    refine ⟨hpa, ?_, ?_⟩
    · intro hpb
      exact hex.1 ⟨hpa, hpb⟩
    · intro hpc
      exact hex.2.1 ⟨hpa, hpc⟩
  · right
    left
    refine ⟨?_, hpb, ?_⟩
    · intro hpa
      exact hex.1 ⟨hpa, hpb⟩
    · intro hpc
      exact hex.2.2 ⟨hpb, hpc⟩
  · right
    right
    refine ⟨?_, ?_, hpc⟩
    · intro hpa
      exact hex.2.1 ⟨hpa, hpc⟩
    · intro hpb
      exact hex.2.2 ⟨hpb, hpc⟩

#print axioms MCore.T28_prime_of_a_divides_frey_discriminant
#print axioms MCore.T28_prime_of_b_divides_frey_discriminant
#print axioms MCore.T28_prime_of_c_divides_frey_discriminant
#print axioms MCore.T28_frey_odd_prime_support_iff
#print axioms MCore.T28_pairwise_prime_exclusive
#print axioms MCore.T28_frey_odd_prime_exactly_one_base

end MCore
