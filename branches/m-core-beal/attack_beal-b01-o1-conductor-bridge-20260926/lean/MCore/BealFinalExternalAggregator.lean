import MCore.BealFastExternalEndpoint
import MCore.BealMasterExternalProof
import MCore.K7

namespace MCore

/-! FINAL EXTERNAL AGGREGATOR

All external claims are represented by typed evidence. Infrastructure GREEN
never promotes a mathematical OPEN_MATH claim.
-/

inductive BealAggregatorClaimState
  | greenInfrastructure
  | openMath
  | proved
  | refuted
  deriving DecidableEq, Repr

structure BealAggregatorClaim where
  id : String
  state : BealAggregatorClaimState
  statement : Prop

def BealClaimInfrastructure : BealAggregatorClaim :=
  { id := "BEAL-INFRASTRUCTURE"
    state := .greenInfrastructure
    statement := True }

def BealClaimFastEndpoint : BealAggregatorClaim :=
  { id := "BEAL-COMMON-DIVISOR-PRODUCER"
    state := .openMath
    statement := Nonempty BealCommonDivisorProducer }

def BealClaimConjecture : BealAggregatorClaim :=
  { id := "BEAL-CONJECTURE"
    state := .openMath
    statement := BealConjecture }

/-- Proof-side external payload. It can only be built from the real minimal
    endpoint inhabitant; no status flag can manufacture this object. -/
structure BealAggregatorProofPayload where
  producer : BealCommonDivisorProducer

def BealAggregatorProofPayload.toBeal
    (P : BealAggregatorProofPayload) : BealConjecture :=
  commonDivisorProducer_closes_beal P.producer

def BealAggregatorProofPayload.toKernelCertificate
    (P : BealAggregatorProofPayload) : ProofCertificate provedBealNode :=
  certifyBeal P.toBeal

/-- Refutation-side external payload. -/
structure BealAggregatorRefutationPayload where
  witness : BealCounterexampleWitness

def BealAggregatorRefutationPayload.toCertificate
    (R : BealAggregatorRefutationPayload) : BealRefutationCertificate :=
  R.witness.toRefutation

theorem beal_external_payloads_exclusive
    (P : BealAggregatorProofPayload)
    (R : BealAggregatorRefutationPayload) : False :=
  proof_refutation_exclusive
    ⟨commonDivisorProducer_closes_beal P.producer⟩
    R.toCertificate

inductive BealAggregatorExternalResolution
  | openMath
  | proved (payload : BealAggregatorProofPayload)
  | refuted (payload : BealAggregatorRefutationPayload)

def BealAggregatorExternalCurrent : BealAggregatorExternalResolution := .openMath

#print axioms MCore.BealAggregatorProofPayload.toBeal
#print axioms MCore.BealAggregatorProofPayload.toKernelCertificate
#print axioms MCore.beal_external_payloads_exclusive

end MCore
