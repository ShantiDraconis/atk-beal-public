import MCore.BealFastExternalEndpoint
import MCore.BealMasterExternalProof
import MCore.K7

namespace MCore

/-! FINAL EXTERNAL AGGREGATOR

All external claims are represented by typed evidence. Infrastructure GREEN
never promotes a mathematical OPEN_MATH claim.
-/

inductive BealExternalClaimState
  | greenInfrastructure
  | openMath
  | proved
  | refuted
  deriving DecidableEq, Repr

structure BealExternalClaim where
  id : String
  state : BealExternalClaimState
  statement : Prop

def BealClaimInfrastructure : BealExternalClaim :=
  { id := "BEAL-INFRASTRUCTURE"
    state := .greenInfrastructure
    statement := True }

def BealClaimFastEndpoint : BealExternalClaim :=
  { id := "BEAL-COMMON-DIVISOR-PRODUCER"
    state := .openMath
    statement := Nonempty BealCommonDivisorProducer }

def BealClaimConjecture : BealExternalClaim :=
  { id := "BEAL-CONJECTURE"
    state := .openMath
    statement := BealConjecture }

/-- Proof-side external payload. It can only be built from the real minimal
    endpoint inhabitant; no status flag can manufacture this object. -/
structure BealExternalProofPayload where
  producer : BealCommonDivisorProducer

def BealExternalProofPayload.toBeal
    (P : BealExternalProofPayload) : BealConjecture :=
  commonDivisorProducer_closes_beal P.producer

def BealExternalProofPayload.toKernelCertificate
    (P : BealExternalProofPayload) : ProofCertificate provedBealNode :=
  certifyBeal P.toBeal

/-- Refutation-side external payload. -/
structure BealExternalRefutationPayload where
  witness : BealCounterexampleWitness

def BealExternalRefutationPayload.toCertificate
    (R : BealExternalRefutationPayload) : BealRefutationCertificate :=
  R.witness.toRefutation

theorem beal_external_payloads_exclusive
    (P : BealExternalProofPayload)
    (R : BealExternalRefutationPayload) : False :=
  proof_refutation_exclusive
    ⟨commonDivisorProducer_closes_beal P.producer⟩
    R.toCertificate

inductive BealFinalExternalResolution
  | openMath
  | proved (payload : BealExternalProofPayload)
  | refuted (payload : BealExternalRefutationPayload)

def BealFinalExternalCurrent : BealFinalExternalResolution := .openMath

#print axioms MCore.BealExternalProofPayload.toBeal
#print axioms MCore.BealExternalProofPayload.toKernelCertificate
#print axioms MCore.beal_external_payloads_exclusive

end MCore
