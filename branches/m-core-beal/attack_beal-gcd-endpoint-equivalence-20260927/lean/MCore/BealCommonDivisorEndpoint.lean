import MCore.K10
import MCore.BealAcceptedClosurePipeline

namespace MCore

/--
Narrow endpoint certificate: every admissible Beal datum has a nontrivial
common divisor. K10 then upgrades that divisor to a common prime.
-/
structure BealUniversalCommonDivisorCertificate where
  witness : ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem universalCommonDivisor_to_commonPrime
    (C : BealUniversalCommonDivisorCertificate) :
    ∀ d : BealData, CommonPrime d.a d.b d.c := by
  intro d
  exact (commonPrime_iff_commonDivisor).2 (C.witness d)

def universalCommonDivisor_to_acceptedClosure
    (C : BealUniversalCommonDivisorCertificate) :
    BealAcceptedClosureObject :=
  ⟨universalCommonDivisor_to_commonPrime C⟩

def universalCommonDivisor_to_proofCertificate
    (C : BealUniversalCommonDivisorCertificate) :
    BealProofCertificate :=
  acceptedClosureObject_to_proofCertificate
    (universalCommonDivisor_to_acceptedClosure C)

def universalCommonDivisor_to_externalCertificate
    (C : BealUniversalCommonDivisorCertificate) :
    BealFinalExternalCertificate :=
  acceptedClosureObject_to_externalCertificate
    (universalCommonDivisor_to_acceptedClosure C)

def universalCommonDivisor_to_finalRoot
    (C : BealUniversalCommonDivisorCertificate) :
    BealFinalRoot :=
  acceptedClosureObject_to_finalRoot
    (universalCommonDivisor_to_acceptedClosure C)

/-- The remaining mathematical target after this reduction. -/
def BealCommonDivisorEndpoint : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem commonDivisorEndpoint_closes_beal
    (h : BealCommonDivisorEndpoint) : BealConjecture :=
  universalCommonDivisor_to_commonPrime ⟨h⟩

#print axioms MCore.universalCommonDivisor_to_commonPrime
#print axioms MCore.universalCommonDivisor_to_acceptedClosure
#print axioms MCore.universalCommonDivisor_to_proofCertificate
#print axioms MCore.universalCommonDivisor_to_externalCertificate
#print axioms MCore.universalCommonDivisor_to_finalRoot
#print axioms MCore.commonDivisorEndpoint_closes_beal

end MCore
