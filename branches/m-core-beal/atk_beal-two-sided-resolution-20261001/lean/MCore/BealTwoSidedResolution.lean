import MCore.T59
import MCore.GCDLowerBoundProducer

namespace MCore

/-- Forget the residual refinements and recover the underlying admissible Beal datum. -/
def T59ResidualCandidate.toBealData
    (d : T59ResidualCandidate) : BealData where
  a := d.a
  b := d.b
  c := d.c
  x := d.x
  y := d.y
  z := d.z
  a_pos := d.a_pos
  b_pos := d.b_pos
  c_pos := d.c_pos
  x_gt_two := d.x_reduced.1
  y_gt_two := d.y_reduced.1
  z_gt_two := d.z_reduced.1
  equation := d.equation

/--
A residual candidate cannot possess a common prime divisor, because that would
already give a nontrivial divisor shared by a and b, contradicting pairwise
primitivity.
-/
theorem T59ResidualCandidate.noCommonPrime
    (d : T59ResidualCandidate) :
    ¬ CommonPrime d.a d.b d.c := by
  intro h
  rcases h with ⟨p, hpPrime, hpa, hpb, hpc⟩
  exact d.pairwisePrimitive.1
    ⟨p, hpPrime.1, hpa, hpb⟩

/-- Every concrete residual candidate is therefore a genuine Beal counterexample. -/
theorem T59ResidualCandidate.isCounterexample
    (d : T59ResidualCandidate) :
    BealCounterexample d.toBealData := by
  exact d.noCommonPrime

/-- A single residual candidate closes the negative orientation of Beal. -/
theorem T59ResidualCandidate.refutesBeal
    (d : T59ResidualCandidate) :
    ¬ BealConjecture := by
  exact counterexample_refutes d.toBealData d.isCounterexample

/-- Positive material producer: the exact nested-GCD producer already isolated. -/
abbrev BealPositiveProducer := GCDLowerBoundProducer

/-- Negative material producer: one fully reduced residual counterexample. -/
abbrev BealNegativeProducer := T59ResidualCandidate

def BealMateriallyResolved : Prop :=
  BealPositiveProducer ∨ Nonempty BealNegativeProducer

/--
Either material orientation closes the mathematical Beal endpoint:
positive gives the conjecture, negative gives its negation.
-/
theorem beal_materially_resolved_outcome
    (h : BealMateriallyResolved) :
    BealConjecture ∨ ¬ BealConjecture := by
  rcases h with hp | hn
  · exact Or.inl (bealConjecture_iff_gcdLowerBoundProducer.mpr hp)
  · rcases hn with ⟨d⟩
    exact Or.inr d.refutesBeal

/-- If both orientations are inhabited, the adapters/model are inconsistent. -/
theorem beal_both_material_routes_contradict
    (hp : BealPositiveProducer)
    (hn : Nonempty BealNegativeProducer) :
    False := by
  rcases hn with ⟨d⟩
  exact d.refutesBeal
    (bealConjecture_iff_gcdLowerBoundProducer.mpr hp)

#print axioms MCore.T59ResidualCandidate.noCommonPrime
#print axioms MCore.T59ResidualCandidate.refutesBeal
#print axioms MCore.beal_materially_resolved_outcome
#print axioms MCore.beal_both_material_routes_contradict

end MCore
