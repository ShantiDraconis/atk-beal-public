import MCore.T57

namespace MCore

/-!
T58 — AGGREGATE ALL FIVE RESIDUAL MIXED FAMILIES

This module is pure glue.  It proves that once the five family-specific
elimination certificates exist, every T7-reduced mixed survivor outside the
all-four FLT(4) branch is eliminated.
-/

def T58ResidualSurvivorDomain
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase,
    Survives c →
    T7ReducedExponent c.x ∧
    T7ReducedExponent c.y ∧
    T7ReducedExponent c.z ∧
    T45MixedReducedSignature c.x c.y c.z ∧
    ¬ T49AllFour c.x c.y c.z

structure T58MixedEliminationBundle
    (Survives : T44LoweredNewformCase → Prop) where
  twoFourPrime : T53TwoFourPrimeEliminationCertificate Survives
  oneFourEqualPrimes : T54OneFourEqualPrimesEliminationCertificate Survives
  oneFourDistinctPrimes : T55OneFourDistinctPrimesEliminationCertificate Survives
  twoEqualOddPrimes : T56TwoEqualOddPrimesEliminationCertificate Survives
  threeDistinctOddPrimes : T57ThreeDistinctOddPrimesEliminationCertificate Survives

theorem T58_five_family_bundle_eliminates_residual_survivors
    {Survives : T44LoweredNewformCase → Prop}
    (hDomain : T58ResidualSurvivorDomain Survives)
    (bundle : T58MixedEliminationBundle Survives) :
    T44AllNewformsEliminated Survives := by
  intro c hSurvives
  rcases hDomain c hSurvives with
    ⟨hx, hy, hz, hMixed, hNotAllFour⟩
  have hFive :
      T51MixedFiveFamilySplit c.x c.y c.z :=
    T51_mixed_reduced_five_family_split hMixed hNotAllFour
  rcases hFive with h44p | h4pp | h4pq | hppq | hpqr
  · exact bundle.twoFourPrime.eliminate c hSurvives h44p
  · exact bundle.oneFourEqualPrimes.eliminate c hSurvives h4pp
  · exact bundle.oneFourDistinctPrimes.eliminate c hSurvives h4pq
  · exact bundle.twoEqualOddPrimes.eliminate c hSurvives hppq
  · exact bundle.threeDistinctOddPrimes.eliminate c hSurvives hpqr

/-- Scientific status: the decomposition/glue is formalized, but each field of
    the bundle remains mathematical content to be supplied by real
    conductor/level/newform arguments. -/
def T58ResidualEliminationState : T36GapState := .openBridge

#print axioms MCore.T58_five_family_bundle_eliminates_residual_survivors

end MCore
