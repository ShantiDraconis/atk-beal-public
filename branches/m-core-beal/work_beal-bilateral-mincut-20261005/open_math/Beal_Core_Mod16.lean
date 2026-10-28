import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem pow_mod_congr_local
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

/-- A reduced prime exponent is not divisible by two. -/
theorem oddPrimeExponent_not_even
    {p : Nat}
    (hp : OddPrimeExponent p) :
    ¬ Even p := by
  intro htwo
  rcases hp.1.2 2 htwo with h1 | hp2
  · cases h1
  · have hlt : 2 < 2 := by simpa [hp2] using hp.2
    exact Nat.lt_irrefl 2 hlt

/-- Hence every reduced prime exponent is 1 modulo 2. -/
theorem oddPrimeExponent_mod_two_eq_one
    {p : Nat}
    (hp : OddPrimeExponent p) :
    p % 2 = 1 := by
  have hnot : ¬ 2 ∣ p := oddPrimeExponent_not_even hp
  have hpos : 0 < p % 2 := Nat.emod_pos_of_not_dvd hnot
  have hlt : p % 2 < 2 := Nat.mod_lt p (by decide)
  omega

/-- Every even fourth power is 0 modulo 16, with no Mathlib dependency. -/
theorem even_fourth_mod_sixteen_core
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, rfl⟩
  simp [Nat.mul_pow, Nat.mul_mod]

/--
An odd natural has one of the eight odd residue classes modulo 16.
This finite split is obtained by Presburger arithmetic only.
-/
theorem odd_residue_mod_sixteen_split
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨
    n % 16 = 3 ∨
    n % 16 = 5 ∨
    n % 16 = 7 ∨
    n % 16 = 9 ∨
    n % 16 = 11 ∨
    n % 16 = 13 ∨
    n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

/-- Every odd fourth power is 1 modulo 16, proved by the finite core split. -/
theorem odd_fourth_mod_sixteen_core
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases odd_residue_mod_sixteen_split hn with
    h | h | h | h | h | h | h | h
  all_goals
    have hc : n ^ 4 % 16 = (n % 16) ^ 4 % 16 := by
      apply pow_mod_congr_local
      simp
    rw [hc, h]

/-- Non-even naturals are exactly the odd naturals modulo two. -/
theorem not_even_iff_mod_two_eq_one_core
    (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hmod hdvd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega

#print axioms MCore.BealEffective.OpenMath.oddPrimeExponent_not_even
#print axioms MCore.BealEffective.OpenMath.oddPrimeExponent_mod_two_eq_one
#print axioms MCore.BealEffective.OpenMath.even_fourth_mod_sixteen_core
#print axioms MCore.BealEffective.OpenMath.odd_residue_mod_sixteen_split
#print axioms MCore.BealEffective.OpenMath.odd_fourth_mod_sixteen_core
#print axioms MCore.BealEffective.OpenMath.not_even_iff_mod_two_eq_one_core

end OpenMath
end BealEffective
end MCore
