import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem ofg_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private def oneFourData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem oneFourExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (oneFourData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (oneFourData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (oneFourData r) h)
  exact exactlyOneEven_of_pairwise (oneFourData r) hpw

private theorem oneFour_notEven_mod2_one (n : Nat) :
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

private theorem oneFour_oddResidue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem oneFour_oddFourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases oneFour_oddResidue8 hn with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply ofg_pow_mod_congr
      simp
    rw [hc, h]

private theorem oneFour_evenPow8
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

/-- Residue pressure whenever x=4; y and z need only be >2. -/
def OneFourXGenericPressure (r : ReducedPrimitiveCandidate) : Prop :=
  (Even r.a → r.b ^ r.y % 8 = r.c ^ r.z % 8) ∧
  (Even r.b → r.c ^ r.z % 8 = 1) ∧
  (Even r.c → r.b ^ r.y % 8 = 7)

theorem oneFour_x_generic_pressure
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4) :
    OneFourXGenericPressure r := by
  have hE := oneFourExactlyOneEven r
  constructor
  · intro ha
    have hA8 : r.a ^ 4 % 8 = 0 :=
      oneFour_evenPow8 ha (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, Nat.add_mod, hA8] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (oneFour_notEven_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    have hA8 : r.a ^ 4 % 8 = 1 := oneFour_oddFourth8 haOdd
    have hB8 : r.b ^ r.y % 8 = 0 :=
      oneFour_evenPow8 hb r.y_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, Nat.add_mod, hA8, hB8] at hmod
    omega
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (oneFour_notEven_mod2_one r.a).mp hC.1
    have hA8 : r.a ^ 4 % 8 = 1 := oneFour_oddFourth8 haOdd
    have hC8 : r.c ^ r.z % 8 = 0 :=
      oneFour_evenPow8 hc r.z_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, Nat.add_mod, hA8, hC8] at hmod
    omega

/-- Residue pressure whenever y=4. -/
def OneFourYGenericPressure (r : ReducedPrimitiveCandidate) : Prop :=
  (Even r.b → r.a ^ r.x % 8 = r.c ^ r.z % 8) ∧
  (Even r.a → r.c ^ r.z % 8 = 1) ∧
  (Even r.c → r.a ^ r.x % 8 = 7)

theorem oneFour_y_generic_pressure
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4) :
    OneFourYGenericPressure r := by
  have hE := oneFourExactlyOneEven r
  constructor
  · intro hb
    have hB8 : r.b ^ 4 % 8 = 0 :=
      oneFour_evenPow8 hb (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hy, Nat.add_mod, hB8] at hmod
    omega
  constructor
  · intro ha
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (oneFour_notEven_mod2_one r.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hB8 : r.b ^ 4 % 8 = 1 := oneFour_oddFourth8 hbOdd
    have hA8 : r.a ^ r.x % 8 = 0 :=
      oneFour_evenPow8 ha r.x_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hy, Nat.add_mod, hA8, hB8] at hmod
    omega
  · intro hc
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (oneFour_notEven_mod2_one r.b).mp hC.2.1
    have hB8 : r.b ^ 4 % 8 = 1 := oneFour_oddFourth8 hbOdd
    have hC8 : r.c ^ r.z % 8 = 0 :=
      oneFour_evenPow8 hc r.z_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hy, Nat.add_mod, hB8, hC8] at hmod
    omega

/-- Residue pressure whenever z=4. -/
def OneFourZGenericPressure (r : ReducedPrimitiveCandidate) : Prop :=
  (Even r.a → r.b ^ r.y % 8 = 1) ∧
  (Even r.b → r.a ^ r.x % 8 = 1) ∧
  (Even r.c → (r.a ^ r.x % 8 + r.b ^ r.y % 8) % 8 = 0)

theorem oneFour_z_generic_pressure
    (r : ReducedPrimitiveCandidate)
    (hz : r.z = 4) :
    OneFourZGenericPressure r := by
  have hE := oneFourExactlyOneEven r
  constructor
  · intro ha
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (oneFour_notEven_mod2_one r.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hC8 : r.c ^ 4 % 8 = 1 := oneFour_oddFourth8 hcOdd
    have hA8 : r.a ^ r.x % 8 = 0 :=
      oneFour_evenPow8 ha r.x_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hz, Nat.add_mod, hA8, hC8] at hmod
    omega
  constructor
  · intro hb
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (oneFour_notEven_mod2_one r.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hC8 : r.c ^ 4 % 8 = 1 := oneFour_oddFourth8 hcOdd
    have hB8 : r.b ^ r.y % 8 = 0 :=
      oneFour_evenPow8 hb r.y_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hz, Nat.add_mod, hB8, hC8] at hmod
    omega
  · intro hc
    have hC8 : r.c ^ 4 % 8 = 0 :=
      oneFour_evenPow8 hc (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hz, Nat.add_mod, hC8] at hmod
    exact hmod

/-- One generic residue payload for either (4,p,p) or (4,p,q). -/
def OneFourGenericPressure (r : ReducedPrimitiveCandidate) : Prop :=
  (r.x = 4 ∧ OneFourXGenericPressure r) ∨
  (r.y = 4 ∧ OneFourYGenericPressure r) ∨
  (r.z = 4 ∧ OneFourZGenericPressure r)

theorem oneFourEqual_forces_generic_pressure
    (r : ReducedPrimitiveCandidate)
    (h : OneFourEqualPrimes r.x r.y r.z) :
    OneFourGenericPressure r := by
  rcases h with hx | hy | hz
  · exact Or.inl ⟨hx.1, oneFour_x_generic_pressure r hx.1⟩
  · exact Or.inr (Or.inl ⟨hy.1, oneFour_y_generic_pressure r hy.1⟩)
  · exact Or.inr (Or.inr ⟨hz.1, oneFour_z_generic_pressure r hz.1⟩)

theorem oneFourDistinct_forces_generic_pressure
    (r : ReducedPrimitiveCandidate)
    (h : OneFourDistinctPrimes r.x r.y r.z) :
    OneFourGenericPressure r := by
  rcases h with hx | hy | hz
  · exact Or.inl ⟨hx.1, oneFour_x_generic_pressure r hx.1⟩
  · exact Or.inr (Or.inl ⟨hy.1, oneFour_y_generic_pressure r hy.1⟩)
  · exact Or.inr (Or.inr ⟨hz.1, oneFour_z_generic_pressure r hz.1⟩)

#print axioms MCore.BealEffective.OpenMath.oneFour_x_generic_pressure
#print axioms MCore.BealEffective.OpenMath.oneFour_y_generic_pressure
#print axioms MCore.BealEffective.OpenMath.oneFour_z_generic_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourEqual_forces_generic_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourDistinct_forces_generic_pressure

end OpenMath
end BealEffective
end MCore
