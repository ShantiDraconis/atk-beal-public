import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem ofep_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private def ofepData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem ofepExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (ofepData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (ofepData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (ofepData r) h)
  exact exactlyOneEven_of_pairwise (ofepData r) hpw

private theorem ofepNotEven_mod2_one
    (n : Nat) :
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

private theorem ofepOddResidue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem ofepOddFourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  rcases ofepOddResidue8 hn with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply ofep_pow_mod_congr
      simp
    rw [hc, h]

private theorem ofepEvenPow8
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

/--
Concrete residue consequences for x=4, y=z=p.
No modularity or conductor theorem is assumed.
-/
def OneFourEqualXPressure
    (r : ReducedPrimitiveCandidate) (p : Nat) : Prop :=
  (Even r.a → r.b ^ p % 8 = r.c ^ p % 8) ∧
  (Even r.b → r.c ^ p % 8 = 1) ∧
  (Even r.c → r.b ^ p % 8 = 7)

/-- Produce the x=4 residue pressure directly from the Beal equation. -/
theorem oneFourEqual_x_pressure
    (r : ReducedPrimitiveCandidate)
    (p : Nat)
    (hx : r.x = 4)
    (hy : r.y = p)
    (hz : r.z = p)
    (hp : OddPrimeExponent p) :
    OneFourEqualXPressure r p := by
  have hE := ofepExactlyOneEven r
  constructor
  · intro ha
    have hA8 : r.a ^ 4 % 8 = 0 :=
      ofepEvenPow8 ha (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hA8] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (ofepNotEven_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    have hA8 : r.a ^ 4 % 8 = 1 := ofepOddFourth8 haOdd
    have hB8 : r.b ^ p % 8 = 0 := ofepEvenPow8 hb hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hA8, hB8] at hmod
    omega
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (ofepNotEven_mod2_one r.a).mp hC.1
    have hA8 : r.a ^ 4 % 8 = 1 := ofepOddFourth8 haOdd
    have hC8 : r.c ^ p % 8 = 0 := ofepEvenPow8 hc hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hA8, hC8] at hmod
    omega

/-- Concrete residue consequences for y=4, x=z=p. -/
def OneFourEqualYPressure
    (r : ReducedPrimitiveCandidate) (p : Nat) : Prop :=
  (Even r.b → r.a ^ p % 8 = r.c ^ p % 8) ∧
  (Even r.a → r.c ^ p % 8 = 1) ∧
  (Even r.c → r.a ^ p % 8 = 7)

theorem oneFourEqual_y_pressure
    (r : ReducedPrimitiveCandidate)
    (p : Nat)
    (hy : r.y = 4)
    (hx : r.x = p)
    (hz : r.z = p)
    (hp : OddPrimeExponent p) :
    OneFourEqualYPressure r p := by
  have hE := ofepExactlyOneEven r
  constructor
  · intro hb
    have hB8 : r.b ^ 4 % 8 = 0 :=
      ofepEvenPow8 hb (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hB8] at hmod
    omega
  constructor
  · intro ha
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (ofepNotEven_mod2_one r.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hB8 : r.b ^ 4 % 8 = 1 := ofepOddFourth8 hbOdd
    have hA8 : r.a ^ p % 8 = 0 := ofepEvenPow8 ha hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hA8, hB8] at hmod
    omega
  · intro hc
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (ofepNotEven_mod2_one r.b).mp hC.2.1
    have hB8 : r.b ^ 4 % 8 = 1 := ofepOddFourth8 hbOdd
    have hC8 : r.c ^ p % 8 = 0 := ofepEvenPow8 hc hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hB8, hC8] at hmod
    omega

/-- Concrete residue consequences for z=4, x=y=p. -/
def OneFourEqualZPressure
    (r : ReducedPrimitiveCandidate) (p : Nat) : Prop :=
  (Even r.a → r.b ^ p % 8 = 1) ∧
  (Even r.b → r.a ^ p % 8 = 1) ∧
  (Even r.c → (r.a ^ p % 8 + r.b ^ p % 8) % 8 = 0)

theorem oneFourEqual_z_pressure
    (r : ReducedPrimitiveCandidate)
    (p : Nat)
    (hz : r.z = 4)
    (hx : r.x = p)
    (hy : r.y = p)
    (hp : OddPrimeExponent p) :
    OneFourEqualZPressure r p := by
  have hE := ofepExactlyOneEven r
  constructor
  · intro ha
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (ofepNotEven_mod2_one r.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hC8 : r.c ^ 4 % 8 = 1 := ofepOddFourth8 hcOdd
    have hA8 : r.a ^ p % 8 = 0 := ofepEvenPow8 ha hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hA8, hC8] at hmod
    omega
  constructor
  · intro hb
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (ofepNotEven_mod2_one r.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hC8 : r.c ^ 4 % 8 = 1 := ofepOddFourth8 hcOdd
    have hB8 : r.b ^ p % 8 = 0 := ofepEvenPow8 hb hp.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hB8, hC8] at hmod
    omega
  · intro hc
    have hC8 : r.c ^ 4 % 8 = 0 :=
      ofepEvenPow8 hc (by decide : 2 < (4 : Nat))
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [hx, hy, hz, Nat.add_mod, hC8] at hmod
    exact hmod

/--
Concrete pressure payload for all three placements of the single exponent 4.
Every branch carries an arithmetic consequence, not merely its signature.
-/
def OneFourEqualResiduePressure (r : ReducedPrimitiveCandidate) : Prop :=
  (∃ p, OddPrimeExponent p ∧ r.x = 4 ∧ r.y = p ∧ r.z = p ∧
      OneFourEqualXPressure r p) ∨
  (∃ p, OddPrimeExponent p ∧ r.y = 4 ∧ r.x = p ∧ r.z = p ∧
      OneFourEqualYPressure r p) ∨
  (∃ p, OddPrimeExponent p ∧ r.z = 4 ∧ r.x = p ∧ r.y = p ∧
      OneFourEqualZPressure r p)

/-- Every (4,p,p) signature now produces a concrete residue-pressure payload. -/
theorem oneFourEqualPrimes_forces_residue_pressure
    (r : ReducedPrimitiveCandidate)
    (h : OneFourEqualPrimes r.x r.y r.z) :
    OneFourEqualResiduePressure r := by
  rcases h with hx | hy | hz
  · rcases hx with ⟨hx4, hp, hzy⟩
    exact Or.inl ⟨r.y, hp, hx4, rfl, hzy,
      oneFourEqual_x_pressure r r.y hx4 rfl hzy hp⟩
  · rcases hy with ⟨hy4, hp, hzx⟩
    exact Or.inr (Or.inl ⟨r.x, hp, hy4, rfl, hzx,
      oneFourEqual_y_pressure r r.x hy4 rfl hzx hp⟩)
  · rcases hz with ⟨hz4, hp, hyx⟩
    exact Or.inr (Or.inr ⟨r.x, hp, hz4, rfl, hyx,
      oneFourEqual_z_pressure r r.x hz4 rfl hyx hp⟩)

#print axioms MCore.BealEffective.OpenMath.oneFourEqual_x_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourEqual_y_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourEqual_z_pressure
#print axioms MCore.BealEffective.OpenMath.oneFourEqualPrimes_forces_residue_pressure

end OpenMath
end BealEffective
end MCore
