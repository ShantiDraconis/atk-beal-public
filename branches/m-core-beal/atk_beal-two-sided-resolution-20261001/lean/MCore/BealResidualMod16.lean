import Mathlib
import MCore.BealResidualMod8

namespace MCore

theorem beal_odd_fourth_mod_sixteen
    {n : Nat}
    (hodd : n % 2 = 1) :
    n ^ 4 % 16 = 1 := by
  have hpar : (n % 16) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)).trans hodd
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  interval_cases h : n % 16 <;>
    simp [Nat.pow_mod, h] at hpar ⊢

theorem beal_even_fourth_mod_sixteen
    {n : Nat}
    (heven : 2 ∣ n) :
    n ^ 4 % 16 = 0 := by
  rcases heven with ⟨k, rfl⟩
  simp [pow_succ, Nat.mul_mod]

/--
For the residual family x=y=4, after the impossible c-even orientation is
removed, the equation forces c^z = 1 mod 16.
-/
theorem T59_two_four_forces_rhs_pow_mod_sixteen
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hy : d.y = 4) :
    d.c ^ d.z % 16 = 1 := by
  have hcOdd : ¬ T12Even d.c :=
    T59_no_rhs_even_when_x_y_four d hx hy
  rcases d.exactlyOneEven with hA | hB | hC
  ·
    have hbOdd : d.b % 2 = 1 :=
      (T12_not_even_iff_odd d.b).mp hA.2.1
    have hA16 : d.a ^ 4 % 16 = 0 :=
      beal_even_fourth_mod_sixteen hA.1
    have hB16 : d.b ^ 4 % 16 = 1 :=
      beal_odd_fourth_mod_sixteen hbOdd
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  ·
    have haOdd : d.a % 2 = 1 :=
      (T12_not_even_iff_odd d.a).mp hB.1
    have hA16 : d.a ^ 4 % 16 = 1 :=
      beal_odd_fourth_mod_sixteen haOdd
    have hB16 : d.b ^ 4 % 16 = 0 :=
      beal_even_fourth_mod_sixteen hB.2.1
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    simpa [hx, hy, Nat.add_mod, hA16, hB16] using hmod
  · exact False.elim (hcOdd hC.2.2)

/--
The same family therefore has an explicit local residue constraint usable by
any later conductor/newform elimination.
-/
def T59TwoFourLocalResidueConstraint (d : T59ResidualCandidate) : Prop :=
  d.x = 4 -> d.y = 4 -> d.c ^ d.z % 16 = 1

theorem T59_two_four_local_residue_constraint
    (d : T59ResidualCandidate) :
    T59TwoFourLocalResidueConstraint d := by
  intro hx hy
  exact T59_two_four_forces_rhs_pow_mod_sixteen d hx hy

#print axioms MCore.beal_odd_fourth_mod_sixteen
#print axioms MCore.beal_even_fourth_mod_sixteen
#print axioms MCore.T59_two_four_forces_rhs_pow_mod_sixteen

end MCore
