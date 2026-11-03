import MCore.BealFastExternalEndpoint
import MCore.BealMasterExternalProof

namespace MCore

/-! FINAL EXTERNAL CLAIM AGGREGATOR

Single fail-closed object for all currently enabled Beal claims.
Infrastructure claims may be certified independently; scientific promotion
requires an actual proof or refutation inhabitant.
-/

inductive BealExternalClaimState
  | infrastructureCertified
  | openMath
  | proved
  | refuted
  deriving DecidableEq, Repr

structure BealExternalClaim where
  id : String
  state : BealExternalClaimState

/-- Certified infrastructure claims currently exported by this repository. -/
def bealExternalInfrastructureClaims : List BealExternalClaim := [
  ⟨"K10-prime-divisor/commonPrime-commonDivisor-equivalence", .infrastructureCertified⟩,
  ⟨"T60/T36E-genuine-odd-multiplicative-reduction", .infrastructureCertified⟩,
  ⟨"B01-dense-contract-and-atomic-DAG", .infrastructureCertified⟩,
  ⟨"B02-five-family-elimination-contract-DAG", .infrastructureCertified⟩,
  ⟨"THREE-GATE-parallel-infrastructure", .infrastructureCertified⟩,
  ⟨"FAST-ENDPOINT-common-divisor-reduction", .infrastructureCertified⟩,
  ⟨"PROOF-REFUTATION-exclusivity", .infrastructureCertified⟩
]

/-- Scientific claims remain open until their actual mathematical data exists. -/
def bealExternalScientificClaims : List BealExternalClaim := [
  ⟨"B01-exact-conductor-and-lowered-level", .openMath⟩,
  ⟨"B02-residual-newform-elimination", .openMath⟩,
  ⟨"UNIVERSAL-common-divisor-producer", .openMath⟩,
  ⟨"BEAL-CONJECTURE", .openMath⟩
]

/-- Minimal proof-side payload for external scientific issuance. -/
structure BealExternalProofPayload where
  producer : BealCommonDivisorProducer

def BealExternalProofPayload.toFastProof
    (P : BealExternalProofPayload) : BealFastExternalProof :=
  { endpoint := P.producer }

theorem BealExternalProofPayload.closes
    (P : BealExternalProofPayload) : BealConjecture :=
  P.toFastProof.closes

def BealExternalProofPayload.toProofCertificate
    (P : BealExternalProofPayload) : BealProofCertificate :=
  P.toFastProof.toCertificate

/-- Refutation-side payload is necessarily one explicit counterexample. -/
structure BealExternalRefutationPayload where
  witness : BealCounterexampleWitness

def BealExternalRefutationPayload.toCertificate
    (R : BealExternalRefutationPayload) : BealRefutationCertificate :=
  R.witness.toRefutation

theorem beal_external_proof_refutation_exclusive
    (P : BealExternalProofPayload)
    (R : BealExternalRefutationPayload) : False :=
  proof_refutation_exclusive P.toProofCertificate R.toCertificate

/-- Final external certificate is data-valued and can only be scientifically
    issued from one genuine mathematical lane. -/
inductive BealFinalExternalCertificate
  | proof (payload : BealExternalProofPayload)
  | refutation (payload : BealExternalRefutationPayload)

def BealFinalExternalCertificate.state :
    BealFinalExternalCertificate → BealExternalClaimState
  | .proof _ => .proved
  | .refutation _ => .refuted

def BealFinalExternalPreparatoryState : BealExternalClaimState := .openMath

#print axioms MCore.BealExternalProofPayload.closes
#print axioms MCore.beal_external_proof_refutation_exclusive

end MCore
