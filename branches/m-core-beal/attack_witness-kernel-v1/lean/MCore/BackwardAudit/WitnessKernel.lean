import MCore.BackwardAudit.WithoutOracle

namespace MCore.BackwardAudit

def BealInstanceClosed (d : MCore.BealData) : Prop :=
  MCore.CommonPrime d.a d.b d.c

structure BealWitnessConstructor : Prop where
  construct : ∀ d : MCore.BealData, BealInstanceClosed d

theorem constructor_to_common_prime_contract
    (W : BealWitnessConstructor) :
    CommonPrimeWitnessContract :=
  ⟨W.construct⟩

theorem common_prime_contract_to_constructor
    (W : CommonPrimeWitnessContract) :
    BealWitnessConstructor :=
  ⟨W.witness⟩

theorem beal_constructor_iff_contract :
    BealWitnessConstructor ↔ CommonPrimeWitnessContract :=
  ⟨constructor_to_common_prime_contract, common_prime_contract_to_constructor⟩

theorem beal_constructor_closes
    (W : BealWitnessConstructor) :
    MCore.BealConjecture :=
  witness_contract_closes_beal (constructor_to_common_prime_contract W)

def bealWitnessConstructorBuilt : Bool := false

theorem beal_witness_constructor_still_open :
    bealWitnessConstructorBuilt = false := by rfl

#print axioms beal_constructor_iff_contract
#print axioms beal_constructor_closes
#print axioms beal_witness_constructor_still_open

end MCore.BackwardAudit
