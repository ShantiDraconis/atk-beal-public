import MCore.T43

namespace MCore

/-!
T44 — STEP 8: NEWFORM-ELIMINATION FRONTIER

Newform elimination has two logically distinct obligations:
1. coverage: every surviving lowered case is in the family/table being checked;
2. elimination: every case in that covered family is impossible.

This separation prevents the classical FLT statement "the lowered level is 2
and level 2 has no weight-2 newform" from being silently promoted to mixed
Beal signatures whose lowered level has not been proved to be 2.
-/

/-- Minimal bookkeeping for a lowered modular case. This is deliberately
    syntactic: a later modular-forms implementation supplies the semantic
    predicate saying that such a case actually survives. -/
structure T44LoweredNewformCase where
  x : Nat
  y : Nat
  z : Nat
  ell : Nat
  level : Nat

/-- Every survivor is covered by the elimination domain. -/
def T44NewformCoverage
    (Survives Covered : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase, Survives c → Covered c

/-- Every covered case is eliminated. -/
def T44CoveredNewformElimination
    (Survives Covered : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase, Covered c → ¬ Survives c

/-- Global elimination target. -/
def T44AllNewformsEliminated
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  ∀ c : T44LoweredNewformCase, ¬ Survives c

theorem T44_coverage_and_elimination_close_step8
    {Survives Covered : T44LoweredNewformCase → Prop}
    (hCoverage : T44NewformCoverage Survives Covered)
    (hEliminate : T44CoveredNewformElimination Survives Covered) :
    T44AllNewformsEliminated Survives := by
  intro c hSurvives
  exact hEliminate c (hCoverage c hSurvives) hSurvives

/-- The classical FLT endgame covers level 2. -/
def T44LevelTwoCovered (c : T44LoweredNewformCase) : Prop :=
  c.level = 2

def T44LevelTwoNewformElimination
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  T44CoveredNewformElimination Survives T44LevelTwoCovered

def T44AllSurvivorsLowerToTwo
    (Survives : T44LoweredNewformCase → Prop) : Prop :=
  T44NewformCoverage Survives T44LevelTwoCovered

theorem T44_level_two_endgame_closes_if_coverage_is_proved
    {Survives : T44LoweredNewformCase → Prop}
    (hLevelTwo : T44AllSurvivorsLowerToTwo Survives)
    (hNoLevelTwo : T44LevelTwoNewformElimination Survives) :
    T44AllNewformsEliminated Survives :=
  T44_coverage_and_elimination_close_step8 hLevelTwo hNoLevelTwo

/-- Fail-proof: eliminating level 2 alone cannot imply elimination at arbitrary
    levels. The witness below is a synthetic surviving level-3 case. -/
def T44UniversalLevelTwoPromotion : Prop :=
  ∀ Survives : T44LoweredNewformCase → Prop,
    T44LevelTwoNewformElimination Survives →
    T44AllNewformsEliminated Survives

theorem T44_universal_level_two_promotion_refuted :
    ¬ T44UniversalLevelTwoPromotion := by
  intro h
  let witness : T44LoweredNewformCase :=
    { x := 3, y := 4, z := 5, ell := 3, level := 3 }
  let Survives : T44LoweredNewformCase → Prop :=
    fun c => c = witness
  have hLevelTwo : T44LevelTwoNewformElimination Survives := by
    intro c hc hSurvives
    change c.level = 2 at hc
    change c = witness at hSurvives
    subst c
    change (3 : Nat) = 2 at hc
    exact (by decide : (3 : Nat) ≠ 2) hc
  have hAll : T44AllNewformsEliminated Survives :=
    h Survives hLevelTwo
  have hWitness : Survives witness := by
    rfl
  exact hAll witness hWitness

/-- A complete Step-8 certificate must carry both coverage and elimination,
    never elimination alone. -/
structure T44NewformEliminationCertificate
    (Survives Covered : T44LoweredNewformCase → Prop) where
  coverage : T44NewformCoverage Survives Covered
  eliminateCovered : T44CoveredNewformElimination Survives Covered

theorem T44_certificate_closes_step8
    {Survives Covered : T44LoweredNewformCase → Prop}
    (c : T44NewformEliminationCertificate Survives Covered) :
    T44AllNewformsEliminated Survives :=
  T44_coverage_and_elimination_close_step8
    c.coverage c.eliminateCovered

/-- Exact fail-closed state for Step 8 in the Beal chain. -/
def T44NewformEliminationState : T36GapState :=
  .openBridge

#print axioms MCore.T44_coverage_and_elimination_close_step8
#print axioms MCore.T44_level_two_endgame_closes_if_coverage_is_proved
#print axioms MCore.T44_universal_level_two_promotion_refuted
#print axioms MCore.T44_certificate_closes_step8

end MCore
