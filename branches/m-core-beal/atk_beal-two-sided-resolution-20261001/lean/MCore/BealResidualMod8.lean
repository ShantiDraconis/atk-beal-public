import Mathlib
import MCore.BealTwoSidedResolution

namespace MCore

/-- Every odd natural has fourth power congruent to 1 modulo 8. -/
theorem beal_odd_fourth_mod_eight
    {n : Nat}
    (hodd : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hodd
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  interval_cases h : n % 8 <;>
    simp [Nat.pow_mod, h] at hpar ⊢

/-- Every even natural raised to an exponent > 2 is 0 modulo 8. -/
theorem beal_even_pow_mod_eight
    {n e : Nat}
    (heven : 2 ∣ n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases heven with ⟨k, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  simp [pow_add, pow_succ, Nat.mul_mod]

/--
The residual family x=y=4 cannot have c as the unique even base.
This removes one concrete orientation of T51TwoFourPrime by elementary
modulo-8 arithmetic.
-/
theorem no_two_four_prime_with_even_rhs
    {a b c z : Nat}
    (haOdd : ¬ T12Even a)
    (hbOdd : ¬ T12Even b)
    (hcEven : T12Even c)
    (hz : 2 < z) :
    a ^ 4 + b ^ 4 ≠ c ^ z := by
  intro heq
  have ha : a % 2 = 1 := (T12_not_even_iff_odd a).mp haOdd
  have hb : b % 2 = 1 := (T12_not_even_iff_odd b).mp hbOdd
  have hA8 : a ^ 4 % 8 = 1 := beal_odd_fourth_mod_eight ha
  have hB8 : b ^ 4 % 8 = 1 := beal_odd_fourth_mod_eight hb
  have hC8 : c ^ z % 8 = 0 := beal_even_pow_mod_eight hcEven hz
  have hmod := congrArg (fun n : Nat => n % 8) heq
  rw [Nat.add_mod, hA8, hB8, hC8] at hmod
  norm_num at hmod

/--
A T59 residual candidate whose first two exponents are 4 cannot place the
unique even base on the right-hand side c.
-/
theorem T59_no_rhs_even_when_x_y_four
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hy : d.y = 4) :
    ¬ T12Even d.c := by
  intro hc
  have hExact := d.exactlyOneEven
  have ha : ¬ T12Even d.a := by
    rcases hExact with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact hB.1
    · exact hC.1
  have hb : ¬ T12Even d.b := by
    rcases hExact with hA | hB | hC
    · exact hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact hC.2.1
  have hz : 2 < d.z := d.z_reduced.1
  apply no_two_four_prime_with_even_rhs ha hb hc hz
  simpa [hx, hy] using d.equation

#print axioms MCore.beal_odd_fourth_mod_eight
#print axioms MCore.beal_even_pow_mod_eight
#print axioms MCore.no_two_four_prime_with_even_rhs
#print axioms MCore.T59_no_rhs_even_when_x_y_four

end MCore
