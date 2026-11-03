import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- Forget only the reduction bookkeeping; retain the exact Beal equation. -/
def ReducedPrimitiveCandidate.toBealData
    (r : ReducedPrimitiveCandidate) : BealData where
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

/--
The no-common-prime field of a reduced candidate already forces pairwise
primitivity.  No terminal Beal assumption is used.
-/
theorem reduced_pairwisePrimitive
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro hab
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      ab_pair_forces_common (ReducedPrimitiveCandidate.toBealData r) hab
    exact r.no_common hcommon
  constructor
  · intro hac
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      ac_pair_forces_common (ReducedPrimitiveCandidate.toBealData r) hac
    exact r.no_common hcommon
  · intro hbc
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      bc_pair_forces_common (ReducedPrimitiveCandidate.toBealData r) hbc
    exact r.no_common hcommon

/--
Every reduced primitive candidate has exactly one even base.  This ports the
constructive parity theorem to the actual seven-family object.
-/
theorem reduced_exactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c := by
  exact exactlyOneEven_of_pairwise
    (ReducedPrimitiveCandidate.toBealData r)
    (reduced_pairwisePrimitive r)

/-- A reduced candidate cannot carry a concrete common prime. -/
theorem reduced_noCommonPrime
    (r : ReducedPrimitiveCandidate) :
    ¬ CommonPrime r.a r.b r.c := by
  intro h
  rcases h with ⟨p, hp, hpa, hpb, hpc⟩
  exact r.no_common ⟨p, hp.1, hpa, hpb, hpc⟩

/--
Useful fail-closed packet for the next quartic forcing stage.  All fields are
constructed from the reduced candidate itself; none is an added hypothesis.
-/
structure ReducedPrimitivePressure
    (r : ReducedPrimitiveCandidate) : Prop where
  pairwise : PairwisePrimitive r.a r.b r.c
  exactlyOneEven : ExactlyOneEven r.a r.b r.c
  noCommonPrime : ¬ CommonPrime r.a r.b r.c

def reducedPrimitivePressure
    (r : ReducedPrimitiveCandidate) :
    ReducedPrimitivePressure r where
  pairwise := reduced_pairwisePrimitive r
  exactlyOneEven := reduced_exactlyOneEven r
  noCommonPrime := reduced_noCommonPrime r

#print axioms MCore.BealEffective.OpenMath.reduced_pairwisePrimitive
#print axioms MCore.BealEffective.OpenMath.reduced_exactlyOneEven
#print axioms MCore.BealEffective.OpenMath.reduced_noCommonPrime
#print axioms MCore.BealEffective.OpenMath.reducedPrimitivePressure

end OpenMath
end BealEffective
end MCore
