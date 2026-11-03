import MCore.BealResidualSystem

namespace MCore

/-!
V24: repair the V23 middle-state experiment so that "independent witness" is
not vacuous. This remains search infrastructure only; it proves no Beal
endpoint and introduces no axiom.
-/

structure MiddleCandidateV24 where
  middle : BealData → Prop
  measure : BealData → Nat

def MiddleReachableV24 (M : MiddleCandidateV24) : Prop :=
  ∃ d : BealData, M.middle d

/-- A genuine experimental middle witness must be explicitly separated from
both endpoint labels on the same datum.  This is deliberately strong: if no
such witness exists, the proposed third state fails this experiment. -/
def MiddleHasIndependentWitnessV24 (M : MiddleCandidateV24) : Prop :=
  ∃ d : BealData,
    M.middle d ∧
    ¬ CommonPrime d.a d.b d.c ∧
    ¬ BealCounterexample d

structure MiddleDynamicsV24 (M : MiddleCandidateV24) where
  step : BealData → BealData → Prop
  decreases : ∀ {d d' : BealData}, step d d' → M.measure d' < M.measure d

def MiddleTerminalV24 {M : MiddleCandidateV24}
    (D : MiddleDynamicsV24 M) (d : BealData) : Prop :=
  M.middle d ∧ ¬ ∃ d' : BealData, D.step d d'

def CenterCompressionTargetV24 (M : MiddleCandidateV24)
    (D : MiddleDynamicsV24 M) : Prop :=
  ∀ d : BealData, MiddleTerminalV24 D d → CommonPrime d.a d.b d.c

/-- Negative control: because BealCounterexample is definitionally the
negation of CommonPrime, the proposed independent third truth-state cannot
simultaneously be outside both endpoint labels. -/
theorem no_independent_truth_state_v24 (M : MiddleCandidateV24) :
    ¬ MiddleHasIndependentWitnessV24 M := by
  rintro ⟨d, _hm, hNotCommon, hNotCounter⟩
  exact hNotCounter hNotCommon

end MCore
