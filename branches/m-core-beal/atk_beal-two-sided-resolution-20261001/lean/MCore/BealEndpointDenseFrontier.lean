import MCore.B02DenseScientificFrontier
import MCore.BealFinalMathematicalChain

namespace MCore

/-! UNIVERSAL ENDPOINT DENSE FRONTIER -/

/-- Concrete admissibility view of the original Beal datum. -/
def BealDatumAdmissible (d : BealData) : Prop :=
  0 < d.a ∧ 0 < d.b ∧ 0 < d.c ∧
  2 < d.x ∧ 2 < d.y ∧ 2 < d.z ∧
  d.a ^ d.x + d.b ^ d.y = d.c ^ d.z

theorem bealData_is_admissible (d : BealData) : BealDatumAdmissible d := by
  exact ⟨d.a_pos, d.b_pos, d.c_pos, d.x_gt_two, d.y_gt_two, d.z_gt_two, d.equation⟩

/-- Per-datum terminal witness: an actual common prime with all divisibility facts. -/
structure BealCommonPrimeWitness (d : BealData) where
  p : Nat
  prime : IsPrime p
  dvdA : p ∣ d.a
  dvdB : p ∣ d.b
  dvdC : p ∣ d.c

def BealCommonPrimeWitness.toCommonPrime
    {d : BealData} (W : BealCommonPrimeWitness d) :
    CommonPrime d.a d.b d.c :=
  ⟨W.p, W.prime, W.dvdA, W.dvdB, W.dvdC⟩

/-- Universal terminal producer. This is the exact data object whose
    inhabitant is logically sufficient to prove Beal. -/
structure BealUniversalWitnessProducer where
  produce : ∀ d : BealData, BealCommonPrimeWitness d

def BealUniversalWitnessProducer.toEndpoint
    (P : BealUniversalWitnessProducer) :
    BealUniversalCommonPrimeCertificate :=
  { witness := fun d => (P.produce d).toCommonPrime }

theorem beal_universal_witness_producer_closes
    (P : BealUniversalWitnessProducer) : BealConjecture :=
  universalCommonPrime_closes_beal P.toEndpoint

/-- Explicit refutation producer kept dual and disjoint. -/
structure BealCounterexampleWitness where
  datum : BealData
  noCommonPrime : BealCounterexample datum

def BealCounterexampleWitness.toRefutation
    (W : BealCounterexampleWitness) : BealRefutationCertificate :=
  ⟨W.datum, W.noCommonPrime⟩

theorem proofProducer_counterexample_exclusive
    (P : BealUniversalWitnessProducer)
    (R : BealCounterexampleWitness) : False :=
  proof_refutation_exclusive
    (universalCommonPrime_to_proofCertificate P.toEndpoint)
    R.toRefutation

def BealEndpointDenseFrontier : Type := BealUniversalWitnessProducer

#print axioms MCore.bealData_is_admissible
#print axioms MCore.beal_universal_witness_producer_closes
#print axioms MCore.proofProducer_counterexample_exclusive

end MCore
