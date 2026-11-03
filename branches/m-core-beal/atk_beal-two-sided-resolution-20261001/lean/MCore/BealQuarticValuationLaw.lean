import Mathlib.Data.Nat.Factorization.Basic
import MCore.BealQuarticCompleteOddSupport

namespace MCore

/--
Generic isolated-factor valuation law.

If b^e = A*B*C and q divides A but divides neither B nor C, then every
q-adic multiplicity on the product is concentrated in A. Hence

  v_q(A) = e * v_q(b).

This is unconditional unique-factorization arithmetic.
-/
theorem isolated_factor_factorization_eq_power_multiple
    {A B C b e q : Nat}
    (hA0 : A ≠ 0)
    (hB0 : B ≠ 0)
    (hC0 : C ≠ 0)
    (hb0 : b ≠ 0)
    (heq : b ^ e = A * (B * C))
    (hqB : ¬ q ∣ B)
    (hqC : ¬ q ∣ C) :
    A.factorization q = e * b.factorization q := by
  have hfac := congrArg (fun n : Nat => n.factorization q) heq
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
  rw [Nat.factorization_mul hA0 (mul_ne_zero hB0 hC0),
      Nat.factorization_mul hB0 hC0,
      Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqB,
      Nat.factorization_eq_zero_of_not_dvd hqC] at hfac
  omega

/-- Divisibility form of the isolated-factor valuation law. -/
theorem exponent_dvd_isolated_factor_factorization
    {A B C b e q : Nat}
    (hA0 : A ≠ 0)
    (hB0 : B ≠ 0)
    (hC0 : C ≠ 0)
    (hb0 : b ≠ 0)
    (heq : b ^ e = A * (B * C))
    (hqB : ¬ q ∣ B)
    (hqC : ¬ q ∣ C) :
    e ∣ A.factorization q := by
  rw [isolated_factor_factorization_eq_power_multiple
    hA0 hB0 hC0 hb0 heq hqB hqC]
  exact dvd_mul_right e (b.factorization q)

/--
On x=z=4, every odd prime q dividing c-a occurs in c-a with multiplicity
divisible by the residual exponent y.
-/
theorem T59_xz_four_sub_factorization_multiple
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqsub : q ∣ d.c - d.a) :
    d.y ∣ (d.c - d.a).factorization q := by
  have hfac := T59_xz_four_exact_factorization d hx hz
  have hca_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hA0 : d.c - d.a ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hca_lt)
  have hB0 : d.c + d.a ≠ 0 := by
    exact Nat.ne_of_gt (Nat.add_pos_left d.c d.a_pos)
  have hC0 : d.c ^ 2 + d.a ^ 2 ≠ 0 := by
    have ha2 : 0 < d.a ^ 2 := Nat.pow_pos d.a_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ ha2)
  have hb0 : d.b ≠ 0 := Nat.ne_of_gt d.b_pos
  have hqB : ¬ q ∣ d.c + d.a := by
    intro h
    exact T59_xz_four_linear_factors_odd_prime_disjoint
      d hx hz hq hq2 ⟨hqsub, h⟩
  have hqC : ¬ q ∣ d.c ^ 2 + d.a ^ 2 := by
    intro h
    exact T59_xz_four_sub_quadratic_odd_prime_disjoint
      d hx hz hq hq2 ⟨hqsub, h⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 hb0 hfac hqB hqC

/--
On x=z=4, every odd prime q dividing c+a occurs there with multiplicity
divisible by y.
-/
theorem T59_xz_four_add_factorization_multiple
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqadd : q ∣ d.c + d.a) :
    d.y ∣ (d.c + d.a).factorization q := by
  have hfac0 := T59_xz_four_exact_factorization d hx hz
  have hfac :
      d.b ^ d.y =
        (d.c + d.a) * ((d.c - d.a) * (d.c ^ 2 + d.a ^ 2)) := by
    calc
      d.b ^ d.y =
          (d.c - d.a) * ((d.c + d.a) * (d.c ^ 2 + d.a ^ 2)) := hfac0
      _ = (d.c + d.a) * ((d.c - d.a) * (d.c ^ 2 + d.a ^ 2)) := by
        ring
  have hca_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hA0 : d.c + d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.a_pos)
  have hB0 : d.c - d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hca_lt)
  have hC0 : d.c ^ 2 + d.a ^ 2 ≠ 0 := by
    have ha2 : 0 < d.a ^ 2 := Nat.pow_pos d.a_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ ha2)
  have hb0 : d.b ≠ 0 := Nat.ne_of_gt d.b_pos
  have hqB : ¬ q ∣ d.c - d.a := by
    intro h
    exact T59_xz_four_linear_factors_odd_prime_disjoint
      d hx hz hq hq2 ⟨h, hqadd⟩
  have hqC : ¬ q ∣ d.c ^ 2 + d.a ^ 2 := by
    intro h
    exact T59_xz_four_add_quadratic_odd_prime_disjoint
      d hx hz hq hq2 ⟨hqadd, h⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 hb0 hfac hqB hqC

/--
On x=z=4, every odd prime q dividing the quadratic factor occurs there with
multiplicity divisible by y.
-/
theorem T59_xz_four_quad_factorization_multiple
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqquad : q ∣ d.c ^ 2 + d.a ^ 2) :
    d.y ∣ (d.c ^ 2 + d.a ^ 2).factorization q := by
  have hfac0 := T59_xz_four_exact_factorization d hx hz
  have hfac :
      d.b ^ d.y =
        (d.c ^ 2 + d.a ^ 2) * ((d.c - d.a) * (d.c + d.a)) := by
    calc
      d.b ^ d.y =
          (d.c - d.a) * ((d.c + d.a) * (d.c ^ 2 + d.a ^ 2)) := hfac0
      _ = (d.c ^ 2 + d.a ^ 2) * ((d.c - d.a) * (d.c + d.a)) := by
        ring
  have hca_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hA0 : d.c ^ 2 + d.a ^ 2 ≠ 0 := by
    have ha2 : 0 < d.a ^ 2 := Nat.pow_pos d.a_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ ha2)
  have hB0 : d.c - d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hca_lt)
  have hC0 : d.c + d.a ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.a_pos)
  have hb0 : d.b ≠ 0 := Nat.ne_of_gt d.b_pos
  have hqB : ¬ q ∣ d.c - d.a := by
    intro h
    exact T59_xz_four_sub_quadratic_odd_prime_disjoint
      d hx hz hq hq2 ⟨h, hqquad⟩
  have hqC : ¬ q ∣ d.c + d.a := by
    intro h
    exact T59_xz_four_add_quadratic_odd_prime_disjoint
      d hx hz hq hq2 ⟨h, hqquad⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 hb0 hfac hqB hqC

#print axioms MCore.isolated_factor_factorization_eq_power_multiple
#print axioms MCore.exponent_dvd_isolated_factor_factorization
#print axioms MCore.T59_xz_four_sub_factorization_multiple
#print axioms MCore.T59_xz_four_add_factorization_multiple
#print axioms MCore.T59_xz_four_quad_factorization_multiple

end MCore
