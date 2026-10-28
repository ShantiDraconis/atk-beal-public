import MCore.BealThreeLaneClosure

namespace MCore

/--
Explicit contract for the object the experimental lane asks us to "accept".
No inhabitant is fabricated here.  An inhabitant must itself provide the
universal common-prime witness for every admissible Beal datum.
-/
structure BealAcceptedClosureObject where
  witness : ∀ d : BealData, CommonPrime d.a d.b d.c

/-- Under the accepted closure object, the Beal conjecture follows in the kernel. -/
theorem acceptedClosureObject_closes_beal
    (A : BealAcceptedClosureObject) : BealConjecture :=
  A.witness

/-- Kernel proof certificate derived from the accepted closure object. -/
def acceptedClosureObject_to_proofCertificate
    (A : BealAcceptedClosureObject) : BealProofCertificate :=
  ⟨acceptedClosureObject_closes_beal A⟩

/--
External mathematical certificate.  Inhabiting this object is stronger than
compiling the interface: it contains an actual kernel proof certificate.
-/
structure BealFinalExternalCertificate where
  proof : BealProofCertificate

def acceptedClosureObject_to_externalCertificate
    (A : BealAcceptedClosureObject) : BealFinalExternalCertificate :=
  ⟨acceptedClosureObject_to_proofCertificate A⟩

/-- Logical theorem-bearing final root. -/
structure BealFinalRoot where
  external : BealFinalExternalCertificate

def acceptedClosureObject_to_finalRoot
    (A : BealAcceptedClosureObject) : BealFinalRoot :=
  ⟨acceptedClosureObject_to_externalCertificate A⟩

theorem finalRoot_closes_beal (R : BealFinalRoot) : BealConjecture :=
  R.external.proof.proof

theorem finalRoot_refutation_exclusive
    (R : BealFinalRoot) (C : BealRefutationCertificate) : False :=
  proof_refutation_exclusive R.external.proof C

/--
Fail-closed source state.  It remains unresolved until an actual
BealAcceptedClosureObject inhabitant is supplied.
-/
def BealAcceptedClosurePipelineState : BealResolution := .unresolved

theorem BealAcceptedClosurePipelineState_is_unresolved :
    BealAcceptedClosurePipelineState = .unresolved := by
  rfl

#print axioms MCore.acceptedClosureObject_closes_beal
#print axioms MCore.acceptedClosureObject_to_proofCertificate
#print axioms MCore.acceptedClosureObject_to_externalCertificate
#print axioms MCore.acceptedClosureObject_to_finalRoot
#print axioms MCore.finalRoot_closes_beal
#print axioms MCore.finalRoot_refutation_exclusive
#print axioms MCore.BealAcceptedClosurePipelineState_is_unresolved

end MCore
