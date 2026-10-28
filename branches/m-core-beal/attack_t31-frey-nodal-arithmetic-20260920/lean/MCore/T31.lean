import MCore.T30

namespace MCore

/-- The three pairwise root-collision factors of the Frey cubic are
    u=A^x, v=B^y, and u+v=C^z. Exactly one divisible factor is the elementary
    arithmetic signature of a nodal degeneration. -/
def T31ExactlyOneCollisionFactor (p u v : Nat) : Prop :=
  (p ∣ u ∧ ¬ p ∣ v ∧ ¬ p ∣ u + v) ∨
  (¬ p ∣ u ∧ p ∣ v ∧ ¬ p ∣ u + v) ∨
  (¬ p ∣ u ∧ ¬ p ∣ v ∧ p ∣ u + v)

def T31NodalArithmeticPrime
    (a b c x y z p : Nat) : Prop :=
  IsPrime p ∧
  p ≠ 2 ∧
  T31ExactlyOneCollisionFactor p (a ^ x) (b ^ y)

/-- Exact one-base support implies exact one-collision-factor support. -/
theorem T31_exact_base_support_to_collision
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hexact : T28ExactlyOneBaseSupport p a b c) :
    T31ExactlyOneCollisionFactor p (a ^ x) (b ^ y) := by
  rcases hexact with ha | hb | hc
  · left
    have hax : p ∣ a ^ x :=
      T11_dvd_pow_of_dvd hx ha.1
    refine ⟨hax, ?_, ?_⟩
    · intro hby
      exact ha.2.1 (T27_prime_dvd_pow hp hby)
    · intro hsum
      have hcz : p ∣ c ^ z := by
        rw [← heq]
        exact hsum
      exact ha.2.2 (T27_prime_dvd_pow hp hcz)
  · right
    left
    have hby : p ∣ b ^ y :=
      T11_dvd_pow_of_dvd hy hb.2.1
    refine ⟨?_, hby, ?_⟩
    · intro hax
      exact hb.1 (T27_prime_dvd_pow hp hax)
    · intro hsum
      have hcz : p ∣ c ^ z := by
        rw [← heq]
        exact hsum
      exact hb.2.2 (T27_prime_dvd_pow hp hcz)
  · right
    right
    have hcz : p ∣ c ^ z :=
      T11_dvd_pow_of_dvd hz hc.2.2
    have hsum : p ∣ a ^ x + b ^ y := by
      rw [heq]
      exact hcz
    refine ⟨?_, ?_, hsum⟩
    · intro hax
      exact hc.1 (T27_prime_dvd_pow hp hax)
    · intro hby
      exact hc.2.1 (T27_prime_dvd_pow hp hby)

/-- Conversely, an exact collision factor gives a base divisor and hence a
    divisor of the raw Frey discriminant. -/
theorem T31_collision_to_discriminant
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hcol : T31ExactlyOneCollisionFactor p (a ^ x) (b ^ y)) :
    p ∣ T24FreyDiscriminantBeal a b c x y z := by
  rcases hcol with hu | hv | huv
  · have hpa : p ∣ a := T27_prime_dvd_pow hp hu.1
    exact T28_prime_of_a_divides_frey_discriminant hx hpa
  · have hpb : p ∣ b := T27_prime_dvd_pow hp hv.2.1
    exact T28_prime_of_b_divides_frey_discriminant hy hpb
  · have hcz : p ∣ c ^ z := by
      rw [← heq]
      exact huv.2.2
    have hpc : p ∣ c := T27_prime_dvd_pow hp hcz
    exact T28_prime_of_c_divides_frey_discriminant hz hpc

/-- Raw odd bad-prime support is exactly the nodal arithmetic collision
    condition on the primitive locus. -/
theorem T31_raw_bad_iff_nodal_arithmetic
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c) :
    T30RawOddBadPrime a b c x y z p ↔
      T31NodalArithmeticPrime a b c x y z p := by
  constructor
  · rintro ⟨hp, hp2, hDelta⟩
    have hexact :=
      T28_frey_odd_prime_exactly_one_base hp hp2 hx hy hz hpw hDelta
    exact ⟨hp, hp2,
      T31_exact_base_support_to_collision hp hx hy hz heq hexact⟩
  · rintro ⟨hp, hp2, hcol⟩
    exact ⟨hp, hp2,
      T31_collision_to_discriminant hp hx hy hz heq hcol⟩

/-- Combining T29/T30 with the collision theorem, the c4 arithmetic
    multiplicative pattern and the nodal collision pattern coincide. -/
theorem T31_arithmetic_multiplicative_iff_nodal
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c) :
    T30ArithmeticMultiplicativePrime a b c x y z p ↔
      T31NodalArithmeticPrime a b c x y z p := by
  rw [← T30_raw_bad_iff_arithmetic_multiplicative hx hy hz heq hpw]
  exact T31_raw_bad_iff_nodal_arithmetic hx hy hz heq hpw

#print axioms MCore.T31_exact_base_support_to_collision
#print axioms MCore.T31_collision_to_discriminant
#print axioms MCore.T31_raw_bad_iff_nodal_arithmetic
#print axioms MCore.T31_arithmetic_multiplicative_iff_nodal

end MCore
