import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private def oddData (r : ReducedPrimitiveCandidate) : BealData where
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

private theorem oddExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  have hpw : PairwisePrimitive r.a r.b r.c := by
    constructor
    · intro h
      exact r.no_common (ab_pair_forces_common (oddData r) h)
    · constructor
      · intro h
        exact r.no_common (ac_pair_forces_common (oddData r) h)
      · intro h
        exact r.no_common (bc_pair_forces_common (oddData r) h)
  exact exactlyOneEven_of_pairwise (oddData r) hpw

private theorem oddEvenPow8
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
The universal local parity pressure for a reduced primitive candidate.
It records exactly what the equation says modulo 8 in each location of the
unique even base.
-/
def ReducedMod8ParityPressure (r : ReducedPrimitiveCandidate) : Prop :=
  (Even r.a → r.b ^ r.y % 8 = r.c ^ r.z % 8) ∧
  (Even r.b → r.a ^ r.x % 8 = r.c ^ r.z % 8) ∧
  (Even r.c → (r.a ^ r.x % 8 + r.b ^ r.y % 8) % 8 = 0)

theorem reduced_forces_mod8_parity_pressure
    (r : ReducedPrimitiveCandidate) :
    ReducedMod8ParityPressure r := by
  constructor
  · intro ha
    have hA8 : r.a ^ r.x % 8 = 0 :=
      oddEvenPow8 ha r.x_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hA8] at hmod
    omega
  constructor
  · intro hb
    have hB8 : r.b ^ r.y % 8 = 0 :=
      oddEvenPow8 hb r.y_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hB8] at hmod
    omega
  · intro hc
    have hC8 : r.c ^ r.z % 8 = 0 :=
      oddEvenPow8 hc r.z_reduced.1
    have hmod := congrArg (fun n : Nat => n % 8) r.equation
    change (r.a ^ r.x + r.b ^ r.y) % 8 = r.c ^ r.z % 8 at hmod
    rw [Nat.add_mod, hC8] at hmod
    exact hmod

/--
Material pressure for the (p,p,q) family: the exact exponent signature plus
the local mod-8 consequence forced by the same candidate.
-/
def TwoEqualOddPrimePressure (r : ReducedPrimitiveCandidate) : Prop :=
  TwoEqualOddPrimes r.x r.y r.z ∧ ReducedMod8ParityPressure r

theorem twoEqualOddPrimes_forces_pressure
    (r : ReducedPrimitiveCandidate)
    (h : TwoEqualOddPrimes r.x r.y r.z) :
    TwoEqualOddPrimePressure r :=
  ⟨h, reduced_forces_mod8_parity_pressure r⟩

/--
Material pressure for the fully distinct odd-prime family.
-/
def ThreeDistinctOddPrimePressure (r : ReducedPrimitiveCandidate) : Prop :=
  ThreeDistinctOddPrimes r.x r.y r.z ∧ ReducedMod8ParityPressure r

theorem threeDistinctOddPrimes_forces_pressure
    (r : ReducedPrimitiveCandidate)
    (h : ThreeDistinctOddPrimes r.x r.y r.z) :
    ThreeDistinctOddPrimePressure r :=
  ⟨h, reduced_forces_mod8_parity_pressure r⟩

#print axioms MCore.BealEffective.OpenMath.reduced_forces_mod8_parity_pressure
#print axioms MCore.BealEffective.OpenMath.twoEqualOddPrimes_forces_pressure
#print axioms MCore.BealEffective.OpenMath.threeDistinctOddPrimes_forces_pressure

end OpenMath
end BealEffective
end MCore
