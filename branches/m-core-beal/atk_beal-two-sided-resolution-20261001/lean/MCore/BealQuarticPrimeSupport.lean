import MCore.BealQuarticOddPrimeSeparation

namespace MCore

/--
On x=z=4, every odd prime dividing c-a also divides b.
-/
theorem T59_xz_four_odd_prime_of_c_sub_a_supports_b
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c - d.a) :
    p ∣ d.b := by
  have hfac := T59_xz_four_exact_factorization d hx hz
  have hprod :
      p ∣ d.b ^ d.y := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_left hpdiv
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1) hprod

/--
On x=z=4, every odd prime dividing c+a also divides b.
-/
theorem T59_xz_four_odd_prime_of_c_add_a_supports_b
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c + d.a) :
    p ∣ d.b := by
  have hfac := T59_xz_four_exact_factorization d hx hz
  have hinner :
      p ∣ (d.c + d.a) * (d.c ^ 2 + d.a ^ 2) :=
    T32_dvd_mul_of_dvd_left hpdiv
  have hprod :
      p ∣ d.b ^ d.y := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_right hinner
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1) hprod

/--
Symmetric support transfer on y=z=4.
-/
theorem T59_yz_four_odd_prime_of_c_sub_b_supports_a
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c - d.b) :
    p ∣ d.a := by
  have hfac := T59_yz_four_exact_factorization d hy hz
  have hprod :
      p ∣ d.a ^ d.x := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_left hpdiv
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1) hprod

theorem T59_yz_four_odd_prime_of_c_add_b_supports_a
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hpdiv : p ∣ d.c + d.b) :
    p ∣ d.a := by
  have hfac := T59_yz_four_exact_factorization d hy hz
  have hinner :
      p ∣ (d.c + d.b) * (d.c ^ 2 + d.b ^ 2) :=
    T32_dvd_mul_of_dvd_left hpdiv
  have hprod :
      p ∣ d.a ^ d.x := by
    rw [hfac]
    exact T32_dvd_mul_of_dvd_right hinner
  exact T30_prime_dvd_pow_of_pos hp
    (Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1) hprod

/--
Candidate-specific odd-prime support partition for the quartic residual branches.
-/
structure T59QuarticOddPrimeSupportPacket
    (d : T59ResidualCandidate) : Prop where
  xz_sub :
    d.x = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      p ∣ d.c - d.a -> p ∣ d.b
  xz_add :
    d.x = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      p ∣ d.c + d.a -> p ∣ d.b
  xz_disjoint :
    d.x = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.a ∧ p ∣ d.c + d.a)
  yz_sub :
    d.y = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      p ∣ d.c - d.b -> p ∣ d.a
  yz_add :
    d.y = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      p ∣ d.c + d.b -> p ∣ d.a
  yz_disjoint :
    d.y = 4 -> d.z = 4 ->
    ∀ p : Nat, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.b ∧ p ∣ d.c + d.b)

theorem T59_quartic_odd_prime_support_packet
    (d : T59ResidualCandidate) :
    T59QuarticOddPrimeSupportPacket d where
  xz_sub := fun hx hz p hp _ hdiv =>
    T59_xz_four_odd_prime_of_c_sub_a_supports_b d hx hz hp hdiv
  xz_add := fun hx hz p hp _ hdiv =>
    T59_xz_four_odd_prime_of_c_add_a_supports_b d hx hz hp hdiv
  xz_disjoint := fun hx hz p hp hp2 =>
    T59_xz_four_linear_factors_odd_prime_disjoint d hx hz hp hp2
  yz_sub := fun hy hz p hp _ hdiv =>
    T59_yz_four_odd_prime_of_c_sub_b_supports_a d hy hz hp hdiv
  yz_add := fun hy hz p hp _ hdiv =>
    T59_yz_four_odd_prime_of_c_add_b_supports_a d hy hz hp hdiv
  yz_disjoint := fun hy hz p hp hp2 =>
    T59_yz_four_linear_factors_odd_prime_disjoint d hy hz hp hp2

#print axioms MCore.T59_xz_four_odd_prime_of_c_sub_a_supports_b
#print axioms MCore.T59_xz_four_odd_prime_of_c_add_a_supports_b
#print axioms MCore.T59_quartic_odd_prime_support_packet

end MCore
