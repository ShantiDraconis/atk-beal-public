import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private theorem aobp_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem oddPrime_mod2_one
    {p : Nat}
    (hp : OddPrimeExponent p) :
    p % 2 = 1 := by
  have hnot : ¬ 2 ∣ p := by
    intro h2
    rcases hp.1.2 2 h2 with h1 | hp2
    · cases h1
    · have hlt : 2 < 2 := by
        simpa [hp2] using hp.2
      exact Nat.lt_irrefl 2 hlt
  have hpos : 0 < p % 2 := Nat.emod_pos_of_not_dvd hnot
  have hlt : p % 2 < 2 := Nat.mod_lt p (by decide)
  omega

private theorem mod2_one_repr
    {e : Nat}
    (he : e % 2 = 1) :
    ∃ k : Nat, e = 2 * k + 1 := by
  refine ⟨e / 2, ?_⟩
  have h := Nat.mod_add_div e 2
  rw [he] at h
  simpa [Nat.add_comm] using h.symm

private theorem oddResidue8
    {n : Nat}
    (hn : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hpar : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  omega

private theorem oddSquare_mod8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 2 % 8 = 1 := by
  rcases oddResidue8 hn with h | h | h | h
  all_goals
    have hc : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := by
      apply aobp_pow_mod_congr
      simp
    rw [hc, h]

/--
For odd n and odd exponent e, n^e has the same residue as n modulo 8.
This uses only the core division identity and elementary modular arithmetic.
-/
theorem oddBase_oddExponent_pow_mod8_eq_base
    {n e : Nat}
    (hn : n % 2 = 1)
    (he : e % 2 = 1) :
    n ^ e % 8 = n % 8 := by
  rcases mod2_one_repr he with ⟨k, rfl⟩
  have hs : n ^ 2 % 8 = 1 := oddSquare_mod8 hn
  have hkpow : (n ^ 2) ^ k % 8 = 1 := by
    have hc := aobp_pow_mod_congr
      (a := n ^ 2) (b := 1) (m := 8) (e := k) hs
    simpa using hc
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hkpow]
  simp

private theorem notEven_mod2_one
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

private def allOddData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem allOddExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (allOddData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (allOddData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (allOddData r) h)
  exact exactlyOneEven_of_pairwise (allOddData r) hpw

private theorem evenPow8
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
Base-level mod-8 pressure for a candidate whose three exponents are odd primes.
The powers disappear from the residue statement.
-/
def AllOddPrimeBasePressure (r : ReducedPrimitiveCandidate) : Prop :=
  (Even r.a → r.b % 8 = r.c % 8) ∧
  (Even r.b → r.a % 8 = r.c % 8) ∧
  (Even r.c → (r.a % 8 + r.b % 8) % 8 = 0)

theorem allOddPrime_forces_base_pressure
    (r : ReducedPrimitiveCandidate)
    (hx : OddPrimeExponent r.x)
    (hy : OddPrimeExponent r.y)
    (hz : OddPrimeExponent r.z) :
    AllOddPrimeBasePressure r := by
  have hE := allOddExactlyOneEven r
  have hxOdd := oddPrime_mod2_one hx
  have hyOdd := oddPrime_mod2_one hy
  have hzOdd := oddPrime_mod2_one hz
  constructor
  · intro ha
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (notEven_mod2_one r.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact (notEven_mod2_one r.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hA8 : r.a ^ r.x % 8 = 0 := evenPow8 ha hx.2
    have hB8 := oddBase_oddExponent_pow_mod8_eq_base hbOdd hyOdd
    have hC8 := oddBase_oddExponent_pow_mod8_eq_base hcOdd hzOdd
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hA8, hB8, hC8] at hmod
    omega
  constructor
  · intro hb
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (notEven_mod2_one r.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    have hcOdd : r.c % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (notEven_mod2_one r.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hA8 := oddBase_oddExponent_pow_mod8_eq_base haOdd hxOdd
    have hB8 : r.b ^ r.y % 8 = 0 := evenPow8 hb hy.2
    have hC8 := oddBase_oddExponent_pow_mod8_eq_base hcOdd hzOdd
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hA8, hB8, hC8] at hmod
    omega
  · intro hc
    have haOdd : r.a % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (notEven_mod2_one r.a).mp hC.1
    have hbOdd : r.b % 2 = 1 := by
      rcases hE with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (notEven_mod2_one r.b).mp hC.2.1
    have hA8 := oddBase_oddExponent_pow_mod8_eq_base haOdd hxOdd
    have hB8 := oddBase_oddExponent_pow_mod8_eq_base hbOdd hyOdd
    have hC8 : r.c ^ r.z % 8 = 0 := evenPow8 hc hz.2
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hA8, hB8, hC8] at hmod
    exact hmod

/-- (p,p,q) now forces a base-level residue packet. -/
theorem twoEqualOddPrimes_forces_base_pressure
    (r : ReducedPrimitiveCandidate)
    (h : TwoEqualOddPrimes r.x r.y r.z) :
    AllOddPrimeBasePressure r := by
  rcases h with hxy | hxz | hyz
  · have hyPrime : OddPrimeExponent r.y := by
      simpa [hxy.2.1] using hxy.1
    exact allOddPrime_forces_base_pressure r hxy.1 hyPrime hxy.2.2.1
  · have hzPrime : OddPrimeExponent r.z := by
      simpa [hxz.2.1] using hxz.1
    exact allOddPrime_forces_base_pressure r hxz.1 hxz.2.2.1 hzPrime
  · have hzPrime : OddPrimeExponent r.z := by
      simpa [hyz.2.1] using hyz.1
    exact allOddPrime_forces_base_pressure r hyz.2.2.1 hyz.1 hzPrime

/-- (p,q,r) with all three primes distinct forces the same base-level packet. -/
theorem threeDistinctOddPrimes_forces_base_pressure
    (r : ReducedPrimitiveCandidate)
    (h : ThreeDistinctOddPrimes r.x r.y r.z) :
    AllOddPrimeBasePressure r :=
  allOddPrime_forces_base_pressure r h.1 h.2.1 h.2.2.1

/--
If c is the unique even base in an all-odd-prime signature, the two odd bases
must occupy complementary nonzero residue classes modulo 8.
-/
theorem allOddPrime_cEven_residue_pairs
    (r : ReducedPrimitiveCandidate)
    (hx : OddPrimeExponent r.x)
    (hy : OddPrimeExponent r.y)
    (hz : OddPrimeExponent r.z)
    (hc : Even r.c) :
    (r.a % 8 = 1 ∧ r.b % 8 = 7) ∨
    (r.a % 8 = 3 ∧ r.b % 8 = 5) ∨
    (r.a % 8 = 5 ∧ r.b % 8 = 3) ∨
    (r.a % 8 = 7 ∧ r.b % 8 = 1) := by
  have hE := allOddExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact False.elim (hB.2.2 hc)
    · exact (notEven_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact False.elim (hB.2.2 hc)
    · exact (notEven_mod2_one r.b).mp hC.2.1
  have hsum :=
    (allOddPrime_forces_base_pressure r hx hy hz).2.2 hc
  rcases oddResidue8 haOdd with ha | ha | ha | ha <;>
    rcases oddResidue8 hbOdd with hb | hb | hb | hb <;>
    simp [ha, hb] at hsum ⊢ <;>
    omega

/--
If a is the unique even base, b and c occupy the same odd class modulo 8.
-/
theorem allOddPrime_aEven_equal_residue
    (r : ReducedPrimitiveCandidate)
    (hx : OddPrimeExponent r.x)
    (hy : OddPrimeExponent r.y)
    (hz : OddPrimeExponent r.z)
    (ha : Even r.a) :
    r.b % 8 = r.c % 8 :=
  (allOddPrime_forces_base_pressure r hx hy hz).1 ha

/--
If b is the unique even base, a and c occupy the same odd class modulo 8.
-/
theorem allOddPrime_bEven_equal_residue
    (r : ReducedPrimitiveCandidate)
    (hx : OddPrimeExponent r.x)
    (hy : OddPrimeExponent r.y)
    (hz : OddPrimeExponent r.z)
    (hb : Even r.b) :
    r.a % 8 = r.c % 8 :=
  (allOddPrime_forces_base_pressure r hx hy hz).2.1 hb

#print axioms MCore.BealEffective.OpenMath.oddBase_oddExponent_pow_mod8_eq_base
#print axioms MCore.BealEffective.OpenMath.allOddPrime_forces_base_pressure
#print axioms MCore.BealEffective.OpenMath.twoEqualOddPrimes_forces_base_pressure
#print axioms MCore.BealEffective.OpenMath.threeDistinctOddPrimes_forces_base_pressure
#print axioms MCore.BealEffective.OpenMath.allOddPrime_cEven_residue_pairs
#print axioms MCore.BealEffective.OpenMath.allOddPrime_aEven_equal_residue
#print axioms MCore.BealEffective.OpenMath.allOddPrime_bEven_equal_residue

end OpenMath
end BealEffective
end MCore
