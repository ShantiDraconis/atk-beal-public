import MCore.K10
import MCore.BealSpecification

namespace MCore

/-- Authoritative minimal material target after producer compression. -/
def MinimalBealInhabitant : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem minimalBealInhabitant_iff_BealConjecture :
    MinimalBealInhabitant ↔ BealConjecture := by
  constructor
  · intro h d
    exact (commonPrime_iff_commonDivisor).mpr (h d)
  · intro h d
    exact (commonPrime_iff_commonDivisor).mp (h d)

#print axioms MCore.minimalBealInhabitant_iff_BealConjecture

end MCore
