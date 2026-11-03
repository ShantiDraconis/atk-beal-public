import MCore.T35
import MCore.T43
import MCore.BealFinalExternalAggregator

namespace MCore

/-! BEAL FAST ELIMINATION ENDPOINT

The repository already proves the exact equivalence
  BealConjecture ↔ T35GlobalEliminationBridge.
So the shortest route aligned with the existing Frey chain is to inhabit
`T35GlobalEliminationBridge` directly.  This is an exact reformulation, not
a weakening and not a proof by itself.
-/

structure BealGlobalEliminationProducer where
  eliminate : T35GlobalEliminationBridge

def BealGlobalEliminationProducer.toBeal
    (P : BealGlobalEliminationProducer) : BealConjecture :=
  T35_beal_iff_global_elimination_bridge.mpr P.eliminate

def BealGlobalEliminationProducer.toProofCertificate
    (P : BealGlobalEliminationProducer) : BealProofCertificate :=
  ⟨P.toBeal⟩

noncomputable def beal_to_globalEliminationProducer
    (H : BealConjecture) : BealGlobalEliminationProducer :=
  ⟨T35_beal_iff_global_elimination_bridge.mp H⟩

theorem beal_iff_globalEliminationProducer :
    BealConjecture ↔ Nonempty BealGlobalEliminationProducer := by
  constructor
  · intro H
    exact ⟨beal_to_globalEliminationProducer H⟩
  · rintro ⟨P⟩
    exact P.toBeal

/-! Negative route-pruning mold.

`T43UniversalSingleResidualPrimeRule` is one candidate formulation of a
single-residual-prime strategy.  The repository already proves that it fails
on the admissible exponent triple (3,4,5).  This closes that formulation only;
it does not refute Beal.
-/

def BealSingleResidualRequiredCondition : Prop :=
  ∃ ell : Nat, T43SingleResidualPrimeCompatible ell 3 4 5

theorem singleResidualRule_requires_345 :
    T43UniversalSingleResidualPrimeRule →
    BealSingleResidualRequiredCondition := by
  intro H
  exact H 3 4 5 (by decide) (by decide) (by decide)

theorem singleResidualRule_breaks_345 :
    ¬ BealSingleResidualRequiredCondition := by
  exact T43_no_single_residual_prime_345

theorem beal_single_residual_formulation_falsified :
    T43UniversalSingleResidualPrimeRule →
    ¬ BealSingleResidualRequiredCondition := by
  intro _
  exact singleResidualRule_breaks_345

theorem beal_single_residual_claim_contradiction :
    T43UniversalSingleResidualPrimeRule ∧
      BealSingleResidualRequiredCondition → False := by
  intro H
  exact singleResidualRule_breaks_345 H.2

#print axioms MCore.BealGlobalEliminationProducer.toBeal
#print axioms MCore.beal_iff_globalEliminationProducer
#print axioms MCore.beal_single_residual_formulation_falsified
#print axioms MCore.beal_single_residual_claim_contradiction

end MCore
