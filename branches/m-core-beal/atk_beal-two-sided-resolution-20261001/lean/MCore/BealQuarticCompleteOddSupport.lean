import MCore.BealQuarticThreeBlockSeparation

namespace MCore

/-- On x=z=4, every odd prime dividing the quadratic quartic factor supports b. -/
theorem T59_xz_four_odd_prime_of_quadratic_supports_b
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c ^ 2 + d.a ^ 2) :
    p ∣ d.b := by
  have hfac := T59_xz_four_exact_factorization d hx hz
  have hinner :
      p ∣ (d.c + d.a) * (d.c ^ 2 + d.a ^ 2) :=
    T32_dvd_mul_of_dvd_right hpdiv
  have hprod :
      p ∣ d.b ^ d.y := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_right hinner
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1) hprod

/-- Symmetric support transfer on y=z=4. -/
theorem T59_yz_four_odd_prime_of_quadratic_supports_a
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c ^ 2 + d.b ^ 2) :
    p ∣ d.a := by
  have hfac := T59_yz_four_exact_factorization d hy hz
  have hinner :
      p ∣ (d.c + d.b) * (d.c ^ 2 + d.b ^ 2) :=
    T32_dvd_mul_of_dvd_right hpdiv
  have hprod :
      p ∣ d.a ^ d.x := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_right hinner
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1) hprod

/--
Complete odd-prime block packet for x=z=4.
All three quartic factors have pairwise disjoint odd-prime supports and every
odd prime in any block divides b.
-/
structure T59XZFourOddPrimeBlockPacket
    (d : T59ResidualCandidate) : Prop where
  hx : d.x = 4
  hz : d.z = 4
  sub_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c - d.a -> p ∣ d.b
  add_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c + d.a -> p ∣ d.b
  quad_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c ^ 2 + d.a ^ 2 -> p ∣ d.b
  sub_add_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.a ∧ p ∣ d.c + d.a)
  sub_quad_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2)
  add_quad_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c + d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2)

/-- Complete odd-prime block packet for y=z=4. -/
structure T59YZFourOddPrimeBlockPacket
    (d : T59ResidualCandidate) : Prop where
  hy : d.y = 4
  hz : d.z = 4
  sub_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c - d.b -> p ∣ d.a
  add_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c + d.b -> p ∣ d.a
  quad_support :
    ∀ p, IsPrime p -> p ≠ 2 -> p ∣ d.c ^ 2 + d.b ^ 2 -> p ∣ d.a
  sub_add_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.b ∧ p ∣ d.c + d.b)
  sub_quad_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2)
  add_quad_disjoint :
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c + d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2)

def T59_xz_four_odd_prime_block_packet
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    T59XZFourOddPrimeBlockPacket d where
  hx := hx
  hz := hz
  sub_support := fun p hp _ h =>
    T59_xz_four_odd_prime_of_c_sub_a_supports_b d hx hz hp h
  add_support := fun p hp _ h =>
    T59_xz_four_odd_prime_of_c_add_a_supports_b d hx hz hp h
  quad_support := fun p hp _ h =>
    T59_xz_four_odd_prime_of_quadratic_supports_b d hx hz hp h
  sub_add_disjoint := fun p hp hp2 =>
    T59_xz_four_linear_factors_odd_prime_disjoint d hx hz hp hp2
  sub_quad_disjoint := fun p hp hp2 =>
    T59_xz_four_sub_quadratic_odd_prime_disjoint d hx hz hp hp2
  add_quad_disjoint := fun p hp hp2 =>
    T59_xz_four_add_quadratic_odd_prime_disjoint d hx hz hp hp2

def T59_yz_four_odd_prime_block_packet
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    T59YZFourOddPrimeBlockPacket d where
  hy := hy
  hz := hz
  sub_support := fun p hp _ h =>
    T59_yz_four_odd_prime_of_c_sub_b_supports_a d hy hz hp h
  add_support := fun p hp _ h =>
    T59_yz_four_odd_prime_of_c_add_b_supports_a d hy hz hp h
  quad_support := fun p hp _ h =>
    T59_yz_four_odd_prime_of_quadratic_supports_a d hy hz hp h
  sub_add_disjoint := fun p hp hp2 =>
    T59_yz_four_linear_factors_odd_prime_disjoint d hy hz hp hp2
  sub_quad_disjoint := fun p hp hp2 =>
    T59_yz_four_sub_quadratic_odd_prime_disjoint d hy hz hp hp2
  add_quad_disjoint := fun p hp hp2 =>
    T59_yz_four_add_quadratic_odd_prime_disjoint d hy hz hp hp2

#print axioms MCore.T59_xz_four_odd_prime_of_quadratic_supports_b
#print axioms MCore.T59_yz_four_odd_prime_of_quadratic_supports_a
#print axioms MCore.T59_xz_four_odd_prime_block_packet
#print axioms MCore.T59_yz_four_odd_prime_block_packet

end MCore
