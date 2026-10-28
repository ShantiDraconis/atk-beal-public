import MCore.BealEffectiveKernel

namespace MCore
namespace BealEffective

/-- On the positive Beal domain, excluding gcd3 = 1 is exactly the strict
terminal lower bound. This is constructive and introduces no new hypothesis. -/
theorem gcd3_ne_one_iff_lowerBound (d : BealData) :
    gcd3 d ≠ 1 ↔ 1 < gcd3 d := by
  constructor
  · intro hne
    by_cases hlt : 1 < gcd3 d
    · exact hlt
    · exact False.elim (hne (gcd3_eq_one_of_not_lowerBound d hlt))
  · intro hlt heq
    rw [heq] at hlt
    exact Nat.lt_irrefl 1 hlt

/-- Exact requested reformulation: the proposed "eliminate gcd3 = 1" theorem
is neither weaker nor stronger than the existing terminal obligation. -/
theorem all_gcd3_ne_one_iff_exact_remaining :
    (∀ d : BealData, gcd3 d ≠ 1) ↔ ExactRemainingObligation := by
  constructor
  · intro h d
    exact (gcd3_ne_one_iff_lowerBound d).mp (h d)
  · intro h d
    exact (gcd3_ne_one_iff_lowerBound d).mpr (h d)

/-- Pointwise, excluding gcd3 = 1 is already equivalent to CommonPrime.
Thus K9/K10/GCD reduction transport this content but cannot manufacture it. -/
theorem gcd3_ne_one_iff_commonPrime (d : BealData) :
    gcd3 d ≠ 1 ↔ CommonPrime d.a d.b d.c := by
  exact (gcd3_ne_one_iff_lowerBound d).trans (lowerBound_iff_commonPrime d)

/-- Universal exclusion of gcd3 = 1 is exactly BealConjecture. -/
theorem all_gcd3_ne_one_iff_beal :
    (∀ d : BealData, gcd3 d ≠ 1) ↔ BealConjecture := by
  rw [all_gcd3_ne_one_iff_exact_remaining]
  constructor
  · exact exact_remaining_closes_beal
  · intro h
    apply exact_remaining_iff_gcdLowerBoundProducer.mpr
    exact bealConjecture_iff_gcdLowerBoundProducer.mp h

#print axioms MCore.BealEffective.gcd3_ne_one_iff_lowerBound
#print axioms MCore.BealEffective.all_gcd3_ne_one_iff_exact_remaining
#print axioms MCore.BealEffective.gcd3_ne_one_iff_commonPrime
#print axioms MCore.BealEffective.all_gcd3_ne_one_iff_beal

end BealEffective
end MCore
