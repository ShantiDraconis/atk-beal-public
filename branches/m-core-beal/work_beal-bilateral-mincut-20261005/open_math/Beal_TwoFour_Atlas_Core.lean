import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem atlas_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem neven_iff_mod2_one (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hm hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem odd_res16
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
    n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

private theorem odd_fourth16
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases odd_res16 hn with h | h | h | h | h | h | h | h
  all_goals
    have hc : n ^ 4 % 16 = (n % 16) ^ 4 % 16 := by
      apply atlas_pow_mod_congr
      simp
    rw [hc, h]

private theorem even_fourth16
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, rfl⟩
  simp [Nat.mul_pow, Nat.mul_mod]

private def reducedData (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

private theorem reducedExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (reducedData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (reducedData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (reducedData r) h)
  exact exactlyOneEven_of_pairwise (reducedData r) hpw

/-- Core-only residue atlas for the x=z=4 orientation. -/
theorem twoFour_xz_residue_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4) :
    (Even r.a → r.b ^ r.y % 16 = 1) ∧
    (Even r.b → r.a ^ 4 % 16 = 1) ∧
    (Even r.c → r.b ^ r.y % 16 = 15) := by
  have hE := reducedExactlyOneEven r
  constructor
  · intro ha
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (neven_iff_mod2_one r.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hA16 : r.a ^ 4 % 16 = 0 := even_fourth16 ha
    have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    rw [hx, hz, Nat.add_mod, hA16, hC16] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (neven_iff_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    exact odd_fourth16 haOdd
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (neven_iff_mod2_one r.a).mp hC.1
    have hA16 : r.a ^ 4 % 16 = 1 := odd_fourth16 haOdd
    have hC16 : r.c ^ 4 % 16 = 0 := even_fourth16 hc
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    rw [hx, hz, Nat.add_mod, hA16, hC16] at hmod
    omega

/-- Core-only residue atlas for the y=z=4 orientation. -/
theorem twoFour_yz_residue_atlas
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4) :
    (Even r.a → r.b ^ 4 % 16 = 1) ∧
    (Even r.b → r.a ^ r.x % 16 = 1) ∧
    (Even r.c → r.a ^ r.x % 16 = 15) := by
  have hE := reducedExactlyOneEven r
  constructor
  · intro ha
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (neven_iff_mod2_one r.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    exact odd_fourth16 hbOdd
  constructor
  · intro hb
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (neven_iff_mod2_one r.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hB16 : r.b ^ 4 % 16 = 0 := even_fourth16 hb
    have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    rw [hy, hz, Nat.add_mod, hB16, hC16] at hmod
    omega
  · intro hc
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (neven_iff_mod2_one r.b).mp hC.2.1
    have hB16 : r.b ^ 4 % 16 = 1 := odd_fourth16 hbOdd
    have hC16 : r.c ^ 4 % 16 = 0 := even_fourth16 hc
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    rw [hy, hz, Nat.add_mod, hB16, hC16] at hmod
    omega

private theorem odd_fourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  have hres : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    omega
  rcases hres with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply atlas_pow_mod_congr
      simp
    rw [hc, h]

private theorem even_pow8_gt_two
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  subst e
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod]

/-- The x=y=4 orientation cannot place the even base on the right. -/
theorem twoFour_xy_rhs_not_even_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hE := reducedExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (neven_iff_mod2_one r.a).mp hB.1
    · exact (neven_iff_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (neven_iff_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (neven_iff_mod2_one r.b).mp hC.2.1
  have hA8 : r.a ^ 4 % 8 = 1 := odd_fourth8 haOdd
  have hB8 : r.b ^ 4 % 8 = 1 := odd_fourth8 hbOdd
  have hC8 : r.c ^ r.z % 8 = 0 := even_pow8_gt_two hc r.z_reduced.1
  have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 :=
    congrArg (fun n : Nat => n % 8) r.equation
  change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
  rw [hx, hy, Nat.add_mod, hA8, hB8, hC8] at hmod
  omega

/-- The x=y=4 orientation forces the RHS power to 1 mod 16. -/
theorem twoFour_xy_rhs_pow_mod16_atlas
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hE := reducedExactlyOneEven r
  have hcOdd := twoFour_xy_rhs_not_even_atlas r hx hy
  rcases hE with hA | hB | hC
  ·
    have hbOdd : r.b % 2 = 1 := (neven_iff_mod2_one r.b).mp hA.2.1
    have hA16 : r.a ^ 4 % 16 = 0 := even_fourth16 hA.1
    have hB16 : r.b ^ 4 % 16 = 1 := odd_fourth16 hbOdd
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  ·
    have haOdd : r.a % 2 = 1 := (neven_iff_mod2_one r.a).mp hB.1
    have hA16 : r.a ^ 4 % 16 = 1 := odd_fourth16 haOdd
    have hB16 : r.b ^ 4 % 16 = 0 := even_fourth16 hB.2.1
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  · exact False.elim (hcOdd hC.2.2)

/-- Concrete residue payload for a two-four-prime candidate. -/
def TwoFourResiduePressure (r : ReducedPrimitiveCandidate) : Prop :=
  (r.x = 4 ∧ r.y = 4 ∧ OddPrimeExponent r.z ∧
      r.c ^ r.z % 16 = 1) ∨
  (r.x = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.y ∧
      ((Even r.a → r.b ^ r.y % 16 = 1) ∧
       (Even r.b → r.a ^ 4 % 16 = 1) ∧
       (Even r.c → r.b ^ r.y % 16 = 15))) ∨
  (r.y = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.x ∧
      ((Even r.a → r.b ^ 4 % 16 = 1) ∧
       (Even r.b → r.a ^ r.x % 16 = 1) ∧
       (Even r.c → r.a ^ r.x % 16 = 15)))

/--
Every (4,4,p) reduced candidate is forced into an explicit mod-16 pressure
payload.  This is a strict strengthening of the raw signature classification.
-/
theorem twoFourPrime_forces_residue_pressure
    (r : ReducedPrimitiveCandidate)
    (h : TwoFourPrime r.x r.y r.z) :
    TwoFourResiduePressure r := by
  rcases h with hxy | hxz | hyz
  · exact Or.inl ⟨hxy.1, hxy.2.1, hxy.2.2,
      twoFour_xy_rhs_pow_mod16_atlas r hxy.1 hxy.2.1⟩
  · exact Or.inr (Or.inl ⟨hxz.1, hxz.2.1, hxz.2.2,
      twoFour_xz_residue_atlas r hxz.1 hxz.2.1⟩)
  · exact Or.inr (Or.inr ⟨hyz.1, hyz.2.1, hyz.2.2,
      twoFour_yz_residue_atlas r hyz.1 hyz.2.1⟩)

private theorem atlas_oddPrime_mod2_one
    {p : Nat}
    (hp : OddPrimeExponent p) :
    p % 2 = 1 := by
  have hnot : ¬ 2 ∣ p := by
    intro h2
    rcases hp.1.2 2 h2 with h1 | h2eq
    · cases h1
    · have hlt : 2 < 2 := by simpa [h2eq] using hp.2
      exact Nat.lt_irrefl 2 hlt
  have hpos : 0 < p % 2 := Nat.emod_pos_of_not_dvd hnot
  have hlt : p % 2 < 2 := Nat.mod_lt p (by decide)
  omega

private theorem atlas_odd_exp_mod4_split
    {e : Nat}
    (he : e % 2 = 1) :
    e % 4 = 1 ∨ e % 4 = 3 := by
  have hpar : (e % 4) % 2 = 1 :=
    (Nat.mod_mod_of_dvd e (by decide : 2 ∣ 4)).trans he
  have hlt : e % 4 < 4 := Nat.mod_lt e (by decide)
  omega

private theorem atlas_exp_mod4_repr
    {e r : Nat}
    (hr : e % 4 = r) :
    ∃ k : Nat, e = r + 4 * k := by
  refine ⟨e / 4, ?_⟩
  have h := Nat.mod_add_div e 4
  rw [hr] at h
  exact h.symm

/-- Odd base + odd exponent + power 15 mod16 forces base 15 mod16. -/
theorem odd_pow_mod16_eq_fifteen_forces_base_fifteen_core
    {u e : Nat}
    (huOdd : u % 2 = 1)
    (heOdd : e % 2 = 1)
    (hpow : u ^ e % 16 = 15) :
    u % 16 = 15 := by
  have h4 : u ^ 4 % 16 = 1 := odd_fourth16 huOdd
  have he4 := atlas_odd_exp_mod4_split heOdd
  rcases he4 with he1 | he3
  · rcases atlas_exp_mod4_repr he1 with ⟨k, hk⟩
    have hkpow : (u ^ 4) ^ k % 16 = 1 := by
      have hc := atlas_pow_mod_congr
        (a := u ^ 4) (b := 1) (m := 16) (e := k) h4
      simpa using hc
    have hbase : u ^ e % 16 = u % 16 := by
      rw [hk, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hkpow]
      simp
    rw [hbase] at hpow
    exact hpow
  · rcases atlas_exp_mod4_repr he3 with ⟨k, hk⟩
    have hkpow : (u ^ 4) ^ k % 16 = 1 := by
      have hc := atlas_pow_mod_congr
        (a := u ^ 4) (b := 1) (m := 16) (e := k) h4
      simpa using hc
    have hcube : u ^ e % 16 = u ^ 3 % 16 := by
      rw [hk, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hkpow]
      simp
    rw [hcube] at hpow
    rcases odd_res16 huOdd with h | h | h | h | h | h | h | h
    all_goals try exact h
    all_goals
      have hc : u ^ 3 % 16 = (u % 16) ^ 3 % 16 := by
        apply atlas_pow_mod_congr
        simp
      rw [hc, h] at hpow
      simp at hpow

/-- Orbit C, x=z=4: c even forces b itself to be 15 mod16. -/
theorem twoFour_xz_c_even_forces_b_mod16_fifteen
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hyPrime : OddPrimeExponent r.y)
    (hc : Even r.c) :
    r.b % 16 = 15 := by
  have hE := reducedExactlyOneEven r
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact False.elim (hB.2.2 hc)
    · exact (neven_iff_mod2_one r.b).mp hC.2.1
  have hp :=
    (twoFour_xz_residue_atlas r hx hz).2.2 hc
  exact odd_pow_mod16_eq_fifteen_forces_base_fifteen_core
    hbOdd (atlas_oddPrime_mod2_one hyPrime) hp

/-- Symmetric orbit C, y=z=4: c even forces a itself to be 15 mod16. -/
theorem twoFour_yz_c_even_forces_a_mod16_fifteen
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    (hxPrime : OddPrimeExponent r.x)
    (hc : Even r.c) :
    r.a % 16 = 15 := by
  have hE := reducedExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact False.elim (hB.2.2 hc)
    · exact (neven_iff_mod2_one r.a).mp hC.1
  have hp :=
    (twoFour_yz_residue_atlas r hy hz).2.2 hc
  exact odd_pow_mod16_eq_fifteen_forces_base_fifteen_core
    haOdd (atlas_oddPrime_mod2_one hxPrime) hp

/-- In x=z=4 with b even, the prime-power term is 0 modulo 16. -/
theorem twoFour_xz_b_even_pow_mod16_zero
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hb : Even r.b) :
    r.b ^ r.y % 16 = 0 := by
  have hE := reducedExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.1 hb)
    · exact (neven_iff_mod2_one r.a).mp hB.1
    · exact False.elim (hC.2.1 hb)
  have hcOdd : r.c % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.1 hb)
    · exact (neven_iff_mod2_one r.c).mp hB.2.2
    · exact False.elim (hC.2.1 hb)
  have hA16 : r.a ^ 4 % 16 = 1 := odd_fourth16 haOdd
  have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
  have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
  change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
  rw [hx, hz, Nat.add_mod, hA16, hC16] at hmod
  omega

private theorem even_cube_mod16_zero_forces_mod4_zero
    {n : Nat}
    (hn : Even n)
    (h3 : n ^ 3 % 16 = 0) :
    n % 4 = 0 := by
  have hmod4 : n % 4 = 0 ∨ n % 4 = 2 := by
    have hpar : (n % 4) % 2 = 0 := by
      have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hn
      exact (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans h0
    have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
    omega
  rcases hmod4 with h0 | h2
  · exact h0
  ·
    have hres :
        n % 16 = 2 ∨ n % 16 = 6 ∨ n % 16 = 10 ∨ n % 16 = 14 := by
      have hpar : (n % 16) % 4 = 2 :=
        (Nat.mod_mod_of_dvd n (by decide : 4 ∣ 16)).trans h2
      have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
      omega
    rcases hres with h | h | h | h
    all_goals
      have hc : n ^ 3 % 16 = (n % 16) ^ 3 % 16 := by
        apply atlas_pow_mod_congr
        simp
      rw [hc, h] at h3
      simp at h3

/--
Orbit B split: either the odd prime exponent is 3, in which case the even base
is actually divisible by 4, or the exponent is at least 5.
-/
theorem twoFour_xz_b_even_prime_split
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hyPrime : OddPrimeExponent r.y)
    (hb : Even r.b) :
    (r.y = 3 ∧ r.b % 4 = 0) ∨ 5 ≤ r.y := by
  have hyOdd : r.y % 2 = 1 := atlas_oddPrime_mod2_one hyPrime
  by_cases h3 : r.y = 3
  · left
    refine ⟨h3, ?_⟩
    have hp0 := twoFour_xz_b_even_pow_mod16_zero r hx hz hb
    rw [h3] at hp0
    exact even_cube_mod16_zero_forces_mod4_zero hb hp0
  · right
    have hgt : 2 < r.y := hyPrime.2
    omega

/-- Symmetric orbit-B split for y=z=4 with a even. -/
theorem twoFour_yz_a_even_prime_split
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    (hxPrime : OddPrimeExponent r.x)
    (ha : Even r.a) :
    (r.x = 3 ∧ r.a % 4 = 0) ∨ 5 ≤ r.x := by
  have hxOdd : r.x % 2 = 1 := atlas_oddPrime_mod2_one hxPrime
  have hE := reducedExactlyOneEven r
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (neven_iff_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.1 ha)
    · exact False.elim (hC.1 ha)
  have hcOdd : r.c % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (neven_iff_mod2_one r.c).mp hA.2.2
    · exact False.elim (hB.1 ha)
    · exact False.elim (hC.1 ha)
  have hB16 : r.b ^ 4 % 16 = 1 := odd_fourth16 hbOdd
  have hC16 : r.c ^ 4 % 16 = 1 := odd_fourth16 hcOdd
  have hpow0 : r.a ^ r.x % 16 = 0 := by
    have hmod :
      (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 :=
    congrArg (fun n : Nat => n % 16) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 16 = r.c ^ r.z % 16 at hmod
    rw [hy, hz, Nat.add_mod, hB16, hC16] at hmod
    omega
  by_cases h3 : r.x = 3
  · left
    refine ⟨h3, ?_⟩
    rw [h3] at hpow0
    exact even_cube_mod16_zero_forces_mod4_zero ha hpow0
  · right
    have hgt : 2 < r.x := hxPrime.2
    omega

#print axioms MCore.BealEffective.OpenMath.twoFour_xz_residue_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_yz_residue_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_not_even_atlas
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_pow_mod16_atlas
#print axioms MCore.BealEffective.OpenMath.twoFourPrime_forces_residue_pressure
#print axioms MCore.BealEffective.OpenMath.odd_pow_mod16_eq_fifteen_forces_base_fifteen_core
#print axioms MCore.BealEffective.OpenMath.twoFour_xz_c_even_forces_b_mod16_fifteen
#print axioms MCore.BealEffective.OpenMath.twoFour_yz_c_even_forces_a_mod16_fifteen
#print axioms MCore.BealEffective.OpenMath.twoFour_xz_b_even_prime_split
#print axioms MCore.BealEffective.OpenMath.twoFour_yz_a_even_prime_split

end OpenMath
end BealEffective
end MCore
