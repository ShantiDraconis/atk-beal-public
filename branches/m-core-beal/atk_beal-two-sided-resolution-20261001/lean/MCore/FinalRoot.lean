import MCore.BealFinalExternalCertificate

namespace MCore

def FINAL_EXTERNAL : Type := BealFinalExternalCertificate

def FINAL_ROOT : FINAL_EXTERNAL → (BealConjecture ∨ Nonempty BealRefutationCertificate)
  | .proof P => Or.inl P.closes
  | .refutation R => Or.inr ⟨R.toCertificate⟩

theorem FINAL_PROOF_of_external_proof
    (P : BealExternalProofPayload) :
    BealConjecture :=
  P.closes

#print axioms MCore.FINAL_PROOF_of_external_proof
end MCore
