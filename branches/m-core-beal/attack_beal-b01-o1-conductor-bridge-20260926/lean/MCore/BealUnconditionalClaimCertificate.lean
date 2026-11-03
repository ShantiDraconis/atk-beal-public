import MCore.BealFastExternalEndpoint
import MCore.BealFastEliminationEndpoint
import MCore.BealNegativeClosureRoute

namespace MCore

/-!
BEAL UNCONDITIONAL CLAIM CERTIFICATE

Canonical positive terminal certificate.  This object contains the theorem
itself; therefore it is neither a process marker nor a conditional claim.
Every accepted proof route must end here.
-/

/-- The exact unconditional mathematical claim. -/
structure BealUnconditionalClaimCertificate : Type where
  theoremProof : BealConjecture

/-- Direct theorem enablement. -/
theorem BealUnconditionalClaimCertificate.enableTheorem
    (C : BealUnconditionalClaimCertificate) : BealConjecture :=
  C.theoremProof

/-- Fast terminal producer -> unconditional claim. -/
def BealUnconditionalClaimCertificate.ofCommonDivisorProducer
    (P : BealCommonDivisorProducer) :
    BealUnconditionalClaimCertificate :=
  ⟨commonDivisorProducer_closes_beal P⟩

/-- Exact global-elimination producer -> unconditional claim. -/
def BealUnconditionalClaimCertificate.ofGlobalElimination
    (P : BealGlobalEliminationProducer) :
    BealUnconditionalClaimCertificate :=
  ⟨P.toBeal⟩

/-- Negative-elimination inhabitant -> unconditional positive Beal claim. -/
def BealUnconditionalClaimCertificate.ofNegativeElimination
    (P : BealNegativeClosureInhabitant) :
    BealUnconditionalClaimCertificate :=
  ⟨beal_negative_closure_inhabitant_closes P⟩

/-- Unconditional claim -> kernel proof certificate. -/
def BealUnconditionalClaimCertificate.toProofCertificate
    (C : BealUnconditionalClaimCertificate) :
    BealProofCertificate :=
  ⟨C.theoremProof⟩

/-- Unconditional claim -> fastest exact terminal producer. -/
noncomputable def BealUnconditionalClaimCertificate.toCommonDivisorProducer
    (C : BealUnconditionalClaimCertificate) :
    BealCommonDivisorProducer :=
  beal_to_commonDivisorProducer C.theoremProof

/-- Exact equivalence: inhabiting this certificate is neither weaker nor
stronger than proving Beal. -/
theorem beal_iff_unconditional_claim_certificate :
    BealConjecture ↔ Nonempty BealUnconditionalClaimCertificate := by
  constructor
  · intro h
    exact ⟨⟨h⟩⟩
  · rintro ⟨C⟩
    exact C.enableTheorem

/-- This is the single positive OPEN_MATH target. -/
abbrev BealUnconditionalOpenMath : Type :=
  BealUnconditionalClaimCertificate

#print axioms MCore.BealUnconditionalClaimCertificate.enableTheorem
#print axioms MCore.BealUnconditionalClaimCertificate.ofCommonDivisorProducer
#print axioms MCore.BealUnconditionalClaimCertificate.ofGlobalElimination
#print axioms MCore.BealUnconditionalClaimCertificate.ofNegativeElimination
#print axioms MCore.beal_iff_unconditional_claim_certificate

end MCore
