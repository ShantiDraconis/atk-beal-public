import MCore.OpenMath.BealQ10PrimitiveExclusion
import Init.Data.Nat.Gcd

namespace MCore.OpenMath.BealQ10

open MCore.OpenMath.BealProbe

def Even (n : Nat) : Prop := 2 ∣ n

def ExactlyOneEven (a b c : Nat) : Prop :=
  (Even a ∧ ¬ Even b ∧ ¬ Even c) ∨
  (¬ Even a ∧ Even b ∧ ¬ Even c) ∨
  (¬ Even a ∧ ¬ Even b ∧ Even c)

private theorem not_even_iff_mod_two_eq_one (n : Nat) :
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

private theorem pow_mod_two_one
    {a n : Nat} (ha : a % 2 = 1) :
    a ^ n % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, ha]

private theorem pow_mod_two_zero
    {a n : Nat} (hn : 0 < n) (ha : Even a) :
    a ^ n % 2 = 0 := by
  have hamod : a % 2 = 0 := Nat.mod_eq_zero_of_dvd ha
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ k =>
      rw [Nat.pow_succ, Nat.mul_mod, hamod]
      simp

private theorem all_even_contradicts_primitive
    (d : MCore.BealData)
    (hd : PrimitiveBealSolution d)
    (ha : Even d.a) (hb : Even d.b) (hc : Even d.c) :
    False := by
  have hab : 2 ∣ Nat.gcd d.a d.b := Nat.dvd_gcd ha hb
  have hg : 2 ∣ Nat.gcd (Nat.gcd d.a d.b) d.c := Nat.dvd_gcd hab hc
  have hle : 2 ≤ observedDefect d := by
    exact Nat.le_of_dvd (by
      unfold observedDefect
      exact Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ d.a_pos)) hg
  rw [hd] at hle
  omega

private theorem ab_not_both_even
    (d : MCore.BealData) (hd : PrimitiveBealSolution d) :
    ¬ (Even d.a ∧ Even d.b) := by
  rintro ⟨ha, hb⟩
  have hxpos : 0 < d.x := Nat.lt_trans (by decide : 0 < 2) d.x_gt_two
  have hypos : 0 < d.y := Nat.lt_trans (by decide : 0 < 2) d.y_gt_two
  have hzpos : 0 < d.z := Nat.lt_trans (by decide : 0 < 2) d.z_gt_two
  have hax := pow_mod_two_zero hxpos ha
  have hby := pow_mod_two_zero hypos hb
  by_cases hc : Even d.c
  · exact all_even_contradicts_primitive d hd ha hb hc
  · have hoc := (not_even_iff_mod_two_eq_one d.c).mp hc
    have hcz := pow_mod_two_one (n := d.z) hoc
    have heq := congrArg (fun n : Nat => n % 2) d.equation
    change (d.a ^ d.x + d.b ^ d.y) % 2 = d.c ^ d.z % 2 at heq
    rw [Nat.add_mod, hax, hby, hcz] at heq
    omega

private theorem ac_not_both_even
    (d : MCore.BealData) (hd : PrimitiveBealSolution d) :
    ¬ (Even d.a ∧ Even d.c) := by
  rintro ⟨ha, hc⟩
  have hxpos : 0 < d.x := Nat.lt_trans (by decide : 0 < 2) d.x_gt_two
  have hypos : 0 < d.y := Nat.lt_trans (by decide : 0 < 2) d.y_gt_two
  have hzpos : 0 < d.z := Nat.lt_trans (by decide : 0 < 2) d.z_gt_two
  have hax := pow_mod_two_zero hxpos ha
  have hcz := pow_mod_two_zero hzpos hc
  by_cases hb : Even d.b
  · exact all_even_contradicts_primitive d hd ha hb hc
  · have hob := (not_even_iff_mod_two_eq_one d.b).mp hb
    have hby := pow_mod_two_one (n := d.y) hob
    have heq := congrArg (fun n : Nat => n % 2) d.equation
    change (d.a ^ d.x + d.b ^ d.y) % 2 = d.c ^ d.z % 2 at heq
    rw [Nat.add_mod, hax, hby, hcz] at heq
    omega

private theorem bc_not_both_even
    (d : MCore.BealData) (hd : PrimitiveBealSolution d) :
    ¬ (Even d.b ∧ Even d.c) := by
  rintro ⟨hb, hc⟩
  have hxpos : 0 < d.x := Nat.lt_trans (by decide : 0 < 2) d.x_gt_two
  have hypos : 0 < d.y := Nat.lt_trans (by decide : 0 < 2) d.y_gt_two
  have hzpos : 0 < d.z := Nat.lt_trans (by decide : 0 < 2) d.z_gt_two
  have hby := pow_mod_two_zero hypos hb
  have hcz := pow_mod_two_zero hzpos hc
  by_cases ha : Even d.a
  · exact all_even_contradicts_primitive d hd ha hb hc
  · have hoa := (not_even_iff_mod_two_eq_one d.a).mp ha
    have hax := pow_mod_two_one (n := d.x) hoa
    have heq := congrArg (fun n : Nat => n % 2) d.equation
    change (d.a ^ d.x + d.b ^ d.y) % 2 = d.c ^ d.z % 2 at heq
    rw [Nat.add_mod, hax, hby, hcz] at heq
    omega

private theorem some_base_even (d : MCore.BealData) :
    Even d.a ∨ Even d.b ∨ Even d.c := by
  by_cases ha : Even d.a
  · exact Or.inl ha
  · by_cases hb : Even d.b
    · exact Or.inr (Or.inl hb)
    · by_cases hc : Even d.c
      · exact Or.inr (Or.inr hc)
      · have hoa := (not_even_iff_mod_two_eq_one d.a).mp ha
        have hob := (not_even_iff_mod_two_eq_one d.b).mp hb
        have hoc := (not_even_iff_mod_two_eq_one d.c).mp hc
        have hax := pow_mod_two_one (n := d.x) hoa
        have hby := pow_mod_two_one (n := d.y) hob
        have hcz := pow_mod_two_one (n := d.z) hoc
        have heq := congrArg (fun n : Nat => n % 2) d.equation
        change (d.a ^ d.x + d.b ^ d.y) % 2 = d.c ^ d.z % 2 at heq
        rw [Nat.add_mod, hax, hby, hcz] at heq
        omega

/-- First material arithmetic consequence of Q10's primitive locus. -/
theorem primitive_exactlyOneEven
    (d : MCore.BealData)
    (hd : PrimitiveBealSolution d) :
    ExactlyOneEven d.a d.b d.c := by
  have hab := ab_not_both_even d hd
  have hac := ac_not_both_even d hd
  have hbc := bc_not_both_even d hd
  rcases some_base_even d with ha | hb | hc
  · exact Or.inl ⟨ha, (fun hb => hab ⟨ha, hb⟩), (fun hc => hac ⟨ha, hc⟩)⟩
  · exact Or.inr (Or.inl ⟨(fun ha => hab ⟨ha, hb⟩), hb, (fun hc => hbc ⟨hb, hc⟩)⟩)
  · exact Or.inr (Or.inr ⟨(fun ha => hac ⟨ha, hc⟩), (fun hb => hbc ⟨hb, hc⟩), hc⟩)

#print axioms MCore.OpenMath.BealQ10.primitive_exactlyOneEven

end MCore.OpenMath.BealQ10
