import Mathlib
import MCore.BealTwoFourResidueAtlas

namespace MCore

/-- A prime exponent strictly larger than two is odd. -/
theorem beal_prime_gt_two_mod_two_eq_one
    {p : Nat}
    (hp : IsPrime p)
    (h2 : 2 < p) :
    p % 2 = 1 := by
  have hnot : ¬ 2 ∣ p := by
    intro hdiv
    rcases hp.2 2 hdiv with h1 | hp2
    · norm_num at h1
    · omega
  exact (T12_not_even_iff_odd p).mp hnot

/--
For odd base residue and odd exponent, u^p = 1 mod 16 forces u = 1 mod 16.
The proof is a complete finite residue audit.
-/
theorem odd_pow_mod16_eq_one_forces_base_one
    {u p : Nat}
    (huOdd : u % 2 = 1)
    (hpOdd : p % 2 = 1)
    (hpow : u ^ p % 16 = 1) :
    u % 16 = 1 := by
  have huParity : (u % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd u (by decide : 2 ∣ 16)).trans huOdd
  have huLt : u % 16 < 16 := Nat.mod_lt u (by decide)
  have hpPos : 0 < p := by omega
  interval_cases hu : u % 16 <;>
    simp at huParity
  all_goals
    have hmodpow :
        (u % 16) ^ p % 16 = 1 := by
      simpa [Nat.pow_mod] using hpow
    simp [hu] at hmodpow
  all_goals
    rcases p with _ | p
    · omega
    ·
      simp_all [Nat.pow_succ, Nat.mul_mod]
      omega

/--
Likewise, u^p = -1 mod 16 forces u = -1 mod 16 for odd p.
-/
theorem odd_pow_mod16_eq_fifteen_forces_base_fifteen
    {u p : Nat}
    (huOdd : u % 2 = 1)
    (hpOdd : p % 2 = 1)
    (hpow : u ^ p % 16 = 15) :
    u % 16 = 15 := by
  have huParity : (u % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd u (by decide : 2 ∣ 16)).trans huOdd
  have huLt : u % 16 < 16 := Nat.mod_lt u (by decide)
  have hpPos : 0 < p := by omega
  interval_cases hu : u % 16 <;>
    simp at huParity
  all_goals
    have hmodpow :
        (u % 16) ^ p % 16 = 15 := by
      simpa [Nat.pow_mod] using hpow
    simp [hu] at hmodpow
  all_goals
    rcases p with _ | p
    · omega
    ·
      simp_all [Nat.pow_succ, Nat.mul_mod]
      omega

/--
In the x=y=4 residual family, the right-hand base itself is 1 modulo 16.
-/
theorem T59_two_four_xy_forces_c_mod_sixteen_one
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hy : d.y = 4)
    (hzPrime : IsPrime d.z)
    (hzGt : 2 < d.z) :
    d.c % 16 = 1 := by
  have hcEvenFalse : ¬ T12Even d.c :=
    T59_no_rhs_even_when_x_y_four d hx hy
  have hcOdd : d.c % 2 = 1 :=
    (T12_not_even_iff_odd d.c).mp hcEvenFalse
  have hzOdd : d.z % 2 = 1 :=
    beal_prime_gt_two_mod_two_eq_one hzPrime hzGt
  exact odd_pow_mod16_eq_one_forces_base_one
    hcOdd hzOdd
    (T59_two_four_forces_rhs_pow_mod_sixteen d hx hy)

/--
For x=z=4: if a is the unique even base, then b=1 mod 16; if c is the
unique even base, then b=15 mod 16.
-/
theorem T59_two_four_xz_sharp_residues
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    (hyPrime : IsPrime d.y)
    (hyGt : 2 < d.y) :
    (T12Even d.a -> d.b % 16 = 1) ∧
    (T12Even d.c -> d.b % 16 = 15) := by
  have hyOdd : d.y % 2 = 1 :=
    beal_prime_gt_two_mod_two_eq_one hyPrime hyGt
  have atlas := T59_two_four_xz_residue_atlas d hx hz
  constructor
  · intro ha
    have hbOdd : d.b % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact (T12_not_even_iff_odd d.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    exact odd_pow_mod16_eq_one_forces_base_one hbOdd hyOdd (atlas.1 ha)
  · intro hc
    have hbOdd : d.b % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (T12_not_even_iff_odd d.b).mp hC.2.1
    exact odd_pow_mod16_eq_fifteen_forces_base_fifteen hbOdd hyOdd (atlas.2.2 hc)

/--
For y=z=4: if b is the unique even base, then a=1 mod 16; if c is the
unique even base, then a=15 mod 16.
-/
theorem T59_two_four_yz_sharp_residues
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    (hxPrime : IsPrime d.x)
    (hxGt : 2 < d.x) :
    (T12Even d.b -> d.a % 16 = 1) ∧
    (T12Even d.c -> d.a % 16 = 15) := by
  have hxOdd : d.x % 2 = 1 :=
    beal_prime_gt_two_mod_two_eq_one hxPrime hxGt
  have atlas := T59_two_four_yz_residue_atlas d hy hz
  constructor
  · intro hb
    have haOdd : d.a % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (T12_not_even_iff_odd d.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    exact odd_pow_mod16_eq_one_forces_base_one haOdd hxOdd (atlas.2.1 hb)
  · intro hc
    have haOdd : d.a % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (T12_not_even_iff_odd d.a).mp hC.1
    exact odd_pow_mod16_eq_fifteen_forces_base_fifteen haOdd hxOdd (atlas.2.2 hc)

#print axioms MCore.beal_prime_gt_two_mod_two_eq_one
#print axioms MCore.odd_pow_mod16_eq_one_forces_base_one
#print axioms MCore.odd_pow_mod16_eq_fifteen_forces_base_fifteen
#print axioms MCore.T59_two_four_xy_forces_c_mod_sixteen_one
#print axioms MCore.T59_two_four_xz_sharp_residues
#print axioms MCore.T59_two_four_yz_sharp_residues

end MCore
