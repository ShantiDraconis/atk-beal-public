import MCore.BackwardAudit.WithoutOracle

namespace MCore.BackwardAudit

/-
Material audit:
CommonPrimeWitnessContract stores the full Beal endpoint as a field.
Therefore witness_contract_closes_beal is transport/projection only.
-/
theorem commonPrimeWitness_is_endpoint_projection
    (W : CommonPrimeWitnessContract) :
    BealConjecture :=
  W.witness

#print axioms MCore.BackwardAudit.commonPrimeWitness_is_endpoint_projection

end MCore.BackwardAudit
