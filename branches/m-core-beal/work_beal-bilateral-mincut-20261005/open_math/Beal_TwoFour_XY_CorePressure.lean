import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem xycp_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem notEven_iff_modTwo_eq_one
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

private theorem odd_residue16
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
    n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hn
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  omega

private theorem odd_residue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem odd_fourth_mod16
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  rcases odd_residue16 hn with h | h | h | h | h | h | h | h
  all_goals
    have hc : n ^ 4 % 16 = (n % 16) ^ 4 % 16 := by
      apply xycp_pow_mod_congr
      simp
    rw [hc, h]

private theorem even_fourth_mod16
    {n : Nat}
    (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  simp [Nat.mul_pow, Nat.mul_mod]

private theorem even_pow_mod8_of_gt_two
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  rw [hk, hm]
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem odd_fourth_mod8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases odd_residue8 hn with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply xycp_pow_mod_congr
      simp
    rw [hc, h]

private def xycpData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem xycpPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro hab
    exact r.no_common (ab_pair_forces_common (xycpData r) hab)
  · constructor
    · intro hac
      exact r.no_common (ac_pair_forces_common (xycpData r) hac)
    · intro hbc
      exact r.no_common (bc_pair_forces_common (xycpData r) hbc)

private theorem xycpExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (xycpData r) (xycpPairwise r)

/-- In the x=y=4 orientation, c cannot be the unique even base. -/
theorem twoFour_xy_rhs_not_even
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hExact := xycpExactlyOneEven r
  have haOdd : ¬ Even r.a := by
    rcases hExact with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact hB.1
    · exact hC.1
  have hbOdd : ¬ Even r.b := by
    rcases hExact with hA | hB | hC
    · exact hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact hC.2.1
  have haMod : r.a % 2 = 1 := (notEven_iff_modTwo_eq_one r.a).mp haOdd
  have hbMod : r.b % 2 = 1 := (notEven_iff_modTwo_eq_one r.b).mp hbOdd
  have hA8 : r.a ^ 4 % 8 = 1 := odd_fourth_mod8 haMod
  have hB8 : r.b ^ 4 % 8 = 1 := odd_fourth_mod8 hbMod
  have hC8 : r.c ^ r.z % 8 = 0 :=
    even_pow_mod8_of_gt_two hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  have hbad : (1 + 1) % 8 = 0 := by
    simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
  omega

/-- The x=y=4 orientation forces the right-hand power to be 1 modulo 16. -/
theorem twoFour_xy_rhs_pow_mod16
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    r.c ^ r.z % 16 = 1 := by
  have hcOdd : ¬ Even r.c := twoFour_xy_rhs_not_even r hx hy
  have hExact := xycpExactlyOneEven r
  rcases hExact with hA | hB | hC
  ·
    have hb : r.b % 2 = 1 := (notEven_iff_modTwo_eq_one r.b).mp hA.2.1
    have hA16 := even_fourth_mod16 hA.1
    have hB16 := odd_fourth_mod16 hb
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  ·
    have ha : r.a % 2 = 1 := (notEven_iff_modTwo_eq_one r.a).mp hB.1
    have hA16 := odd_fourth_mod16 ha
    have hB16 := even_fourth_mod16 hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) r.equation
    have h : 1 = r.c ^ r.z % 16 := by
      simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
    exact h.symm
  · exact False.elim (hcOdd hC.2.2)

#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_not_even
#print axioms MCore.BealEffective.OpenMath.twoFour_xy_rhs_pow_mod16

end OpenMath
end BealEffective
end MCore
