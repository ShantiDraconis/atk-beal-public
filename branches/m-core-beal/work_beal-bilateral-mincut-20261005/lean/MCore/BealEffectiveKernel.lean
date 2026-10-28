import MCore.GCDLowerBoundProducer

namespace MCore
namespace BealEffective

/-- Canonical ternary gcd used by the frozen Beal terminal producer. -/
def gcd3 (d : BealData) : Nat :=
  Nat.gcd d.a (Nat.gcd d.b d.c)

/-- Positivity is inherited from the positive Beal domain. -/
theorem gcd3_pos (d : BealData) :
    0 < gcd3 d := by
  unfold gcd3
  exact Nat.gcd_pos_of_pos_left _ d.a_pos

/-- If the terminal strict lower bound fails, positivity forces gcd3 = 1. -/
theorem gcd3_eq_one_of_not_lowerBound
    (d : BealData)
    (h : ¬ 1 < gcd3 d) :
    gcd3 d = 1 := by
  have hle : gcd3 d ≤ 1 := Nat.le_of_not_gt h
  have hone : 1 ≤ gcd3 d := Nat.succ_le_of_lt (gcd3_pos d)
  exact Nat.le_antisymm hle hone

/-- The frozen scalar lower bound is exactly the concrete CommonPrime endpoint. -/
theorem lowerBound_iff_commonPrime (d : BealData) :
    1 < gcd3 d ↔ CommonPrime d.a d.b d.c := by
  constructor
  · intro h
    exact (commonPrime_iff_one_lt_nestedGCD d).mpr (by simpa [gcd3] using h)
  · intro h
    have hg := (commonPrime_iff_one_lt_nestedGCD d).mp h
    simpa [gcd3] using hg

/-- Failure of the scalar endpoint gives a genuine Beal counterexample. -/
theorem failed_lowerBound_gives_counterexample
    (d : BealData)
    (h : ¬ 1 < gcd3 d) :
    BealCounterexample d := by
  unfold BealCounterexample
  intro hp
  exact h ((lowerBound_iff_commonPrime d).mpr hp)

/-- Conversely, a genuine Beal counterexample is exactly failure of the scalar endpoint. -/
theorem counterexample_gives_failed_lowerBound
    (d : BealData)
    (h : BealCounterexample d) :
    ¬ 1 < gcd3 d := by
  intro hg
  exact h ((lowerBound_iff_commonPrime d).mp hg)

/-- Exact pointwise dichotomy, with no semantic wrapper and no new hypothesis. -/
theorem terminal_pointwise_dichotomy (d : BealData) :
    (1 < gcd3 d) ∨ BealCounterexample d := by
  by_cases h : 1 < gcd3 d
  · exact Or.inl h
  · exact Or.inr (failed_lowerBound_gives_counterexample d h)

/-- The unique remaining material theorem after all frozen reductions are reused. -/
def ExactRemainingObligation : Prop :=
  ∀ d : BealData, 1 < gcd3 d

/-- The exact remaining obligation is definitionally the frozen GCD producer. -/
theorem exact_remaining_iff_gcdLowerBoundProducer :
    ExactRemainingObligation ↔ GCDLowerBoundProducer := by
  constructor
  · intro h d
    simpa [gcd3] using h d
  · intro h d
    simpa [gcd3] using h d

/-- Therefore closing the one remaining obligation closes Beal immediately. -/
theorem exact_remaining_closes_beal
    (h : ExactRemainingObligation) :
    BealConjecture := by
  exact bealConjecture_iff_gcdLowerBoundProducer.mpr
    (exact_remaining_iff_gcdLowerBoundProducer.mp h)

/-- A concrete negative witness constructively refutes the remaining obligation. -/
theorem concrete_counterexample_refutes_remaining
    {d : BealData}
    (h : BealCounterexample d) :
    ¬ ExactRemainingObligation := by
  intro hall
  exact h ((lowerBound_iff_commonPrime d).mp (hall d))

#print axioms MCore.BealEffective.gcd3_pos
#print axioms MCore.BealEffective.gcd3_eq_one_of_not_lowerBound
#print axioms MCore.BealEffective.lowerBound_iff_commonPrime
#print axioms MCore.BealEffective.failed_lowerBound_gives_counterexample
#print axioms MCore.BealEffective.counterexample_gives_failed_lowerBound
#print axioms MCore.BealEffective.terminal_pointwise_dichotomy
#print axioms MCore.BealEffective.exact_remaining_iff_gcdLowerBoundProducer
#print axioms MCore.BealEffective.exact_remaining_closes_beal
#print axioms MCore.BealEffective.concrete_counterexample_refutes_remaining

end BealEffective
end MCore
