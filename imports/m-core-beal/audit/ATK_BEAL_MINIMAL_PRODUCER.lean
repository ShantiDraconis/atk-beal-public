import MCore.GCDLowerBoundProducer

namespace MCore

/-- Legacy existential producer, retained only to certify equivalence to the
smaller scalar producer. -/
def CommonDivisorProducer : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

theorem bealConjecture_iff_commonDivisorProducer :
    BealConjecture ↔ CommonDivisorProducer := by
  constructor
  · intro h d
    exact (commonPrime_iff_commonDivisor).mp (h d)
  · intro h d
    exact (commonPrime_iff_commonDivisor).mpr (h d)

theorem commonDivisorProducer_iff_gcdLowerBoundProducer :
    CommonDivisorProducer ↔ GCDLowerBoundProducer := by
  constructor
  · intro h d
    exact (commonDivisor_iff_one_lt_nestedGCD d).mp (h d)
  · intro h d
    exact (commonDivisor_iff_one_lt_nestedGCD d).mpr (h d)

#print axioms MCore.bealConjecture_iff_commonDivisorProducer
#print axioms MCore.bealConjecture_iff_gcdLowerBoundProducer

end MCore
