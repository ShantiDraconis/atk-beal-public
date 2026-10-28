import MCore.T45

namespace MCore

/-!
T46 — STEP 8 SIGNATURE SPLIT

For any survivor whose exponents are T7-reduced, there are exactly two proof
routes relevant to the current newform-elimination ledger:

* equal odd-prime signature: the classical FLT-style single-residual-prime
  route is available;
* mixed reduced signature: T45 proves that no single odd residual prime can
  divide all three exponents, so a separate signature-specific elimination
  argument is required.

This module proves the logical partition and the exact conditions under which
a level-2 elimination closes the equal-prime branch.
-/

/-- All surviving modular cases have T7-reduced signatures. -/
def T46ReducedSurvivors
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase,
    Survives c →
    T7ReducedExponent c.x ∧
    T7ReducedExponent c.y ∧
    T7ReducedExponent c.z

/-- Elimination of the equal-prime branch. -/
def T46EqualPrimeBranchEliminated
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase,
    Survives c →
    T45EqualOddPrimeSignature c.x c.y c.z →
    False

/-- Elimination of the genuinely mixed-signature branch. -/
def T46MixedBranchEliminated
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase,
    Survives c →
    T45MixedReducedSignature c.x c.y c.z →
    False

/-- Every reduced survivor is either equal-prime or mixed. -/
theorem T46_reduced_survivor_signature_split
    {Survives : T44LoweredNewformCase → Prop}
    (hReduced : T46ReducedSurvivors Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c) :
    T45EqualOddPrimeSignature c.x c.y c.z ∨
      T45MixedReducedSignature c.x c.y c.z := by
  classical
  rcases hReduced c hSurvives with ⟨hx, hy, hz⟩
  by_cases hEq : T45EqualOddPrimeSignature c.x c.y c.z
  · exact Or.inl hEq
  · exact Or.inr ⟨hx, hy, hz, hEq⟩

/-- If both signature branches are eliminated, all reduced survivors vanish. -/
theorem T46_two_signature_branches_close_step8
    {Survives : T44LoweredNewformCase → Prop}
    (hReduced : T46ReducedSurvivors Survives)
    (hEqual : T46EqualPrimeBranchEliminated Survives)
    (hMixed : T46MixedBranchEliminated Survives) :
    T44AllNewformsEliminated Survives := by
  intro c hSurvives
  rcases T46_reduced_survivor_signature_split hReduced hSurvives with hEq | hMixedSig
  · exact hEqual c hSurvives hEq
  · exact hMixed c hSurvives hMixedSig

/-- Coverage theorem required to use the classical FLT level-2 endgame on the
    equal-prime branch. -/
def T46EqualPrimeBranchLowersToTwo
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase,
    Survives c →
    T45EqualOddPrimeSignature c.x c.y c.z →
    c.level = 2

/-- A certified level-2 newform elimination closes the equal-prime branch once
    the equal-prime lowering-to-2 coverage theorem is supplied. -/
theorem T46_level_two_closes_equal_prime_branch
    {Survives : T44LoweredNewformCase → Prop}
    (hLowerToTwo : T46EqualPrimeBranchLowersToTwo Survives)
    (hNoLevelTwo : T44LevelTwoNewformElimination Survives) :
    T46EqualPrimeBranchEliminated Survives := by
  intro c hSurvives hEqual
  have hLevel : T44LevelTwoCovered c :=
    hLowerToTwo c hSurvives hEqual
  exact hNoLevelTwo c hLevel hSurvives

/-- Final Step-8 decomposition:
    reduced-signature coverage
    + equal-prime level lowering to 2
    + no level-2 survivor
    + mixed-signature elimination
    is sufficient to eliminate every newform case. -/
theorem T46_step8_reduced_to_level_two_plus_mixed
    {Survives : T44LoweredNewformCase → Prop}
    (hReduced : T46ReducedSurvivors Survives)
    (hLowerToTwo : T46EqualPrimeBranchLowersToTwo Survives)
    (hNoLevelTwo : T44LevelTwoNewformElimination Survives)
    (hMixed : T46MixedBranchEliminated Survives) :
    T44AllNewformsEliminated Survives := by
  apply T46_two_signature_branches_close_step8 hReduced
  · exact T46_level_two_closes_equal_prime_branch hLowerToTwo hNoLevelTwo
  · exact hMixed

/-- The only genuinely new Step-8 obligation after the classical equal-prime
    level-2 branch is discharged. -/
structure T46Step8ResidualCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  reduced : T46ReducedSurvivors Survives
  equalPrimeLowersToTwo : T46EqualPrimeBranchLowersToTwo Survives
  noLevelTwo : T44LevelTwoNewformElimination Survives
  mixedElimination : T46MixedBranchEliminated Survives

theorem T46_certificate_closes_step8
    {Survives : T44LoweredNewformCase → Prop}
    (c : T46Step8ResidualCertificate Survives) :
    T44AllNewformsEliminated Survives :=
  T46_step8_reduced_to_level_two_plus_mixed
    c.reduced c.equalPrimeLowersToTwo c.noLevelTwo c.mixedElimination

#print axioms MCore.T46_reduced_survivor_signature_split
#print axioms MCore.T46_two_signature_branches_close_step8
#print axioms MCore.T46_level_two_closes_equal_prime_branch
#print axioms MCore.T46_step8_reduced_to_level_two_plus_mixed
#print axioms MCore.T46_certificate_closes_step8

end MCore
