import MCore.K10
import MCore.BealSpecification

namespace MCore
namespace Attack

/-- Exact non-prime formulation of the remaining Beal endpoint. -/
def UniversalCommonDivisor : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

/--
The endpoint is exactly equivalent to the universal nontrivial-common-divisor
producer once K10's proved prime-divisor extraction is reused.
-/
theorem bealConjecture_iff_universalCommonDivisor :
    BealConjecture ↔ UniversalCommonDivisor := by
  constructor
  · intro h d
    exact (commonPrime_iff_commonDivisor.mp (h d))
  · intro h d
    exact (commonPrime_iff_commonDivisor.mpr (h d))

def terminalProducerStatus : String :=
  "OPEN_MATH: prove UniversalCommonDivisor; prime extraction is already PROVED/REUSE"

#print axioms bealConjecture_iff_universalCommonDivisor

end Attack
end MCore
