import MCore.K10
import MCore.BealSpecification

namespace MCore

/-- Canonical direct-producer compression for Beal.

The terminal mathematical content is exactly the construction of a nontrivial
common divisor for every admissible Beal datum.  K10 already proves that such a
divisor is equivalent to a common prime divisor, so modular/conductor machinery
is a strategy for producing this object, not part of the endpoint type itself.
-/
def CommonDivisorProducer : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem bealConjecture_iff_commonDivisorProducer :
    BealConjecture ↔ CommonDivisorProducer := by
  constructor
  · intro h d
    exact (commonPrime_iff_commonDivisor).mp (h d)
  · intro h d
    exact (commonPrime_iff_commonDivisor).mpr (h d)

#print axioms MCore.bealConjecture_iff_commonDivisorProducer

end MCore
