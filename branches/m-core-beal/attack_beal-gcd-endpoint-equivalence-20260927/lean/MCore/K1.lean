import MCore.K0

namespace MCore

inductive ResearchRoute where
  | massGap | criticalLine | complexityLowerBound | cycleAlgebraicity | rankBridge | commonPrime
  deriving DecidableEq, Repr

structure K1Target where
  route : ResearchRoute
  status : SignatureStatus := .openBridge

/-- Beal K1: common-prime/Diophantine route remains an open bridge. -/
def k1Target : K1Target := ⟨.commonPrime, .openBridge⟩

theorem k1_status_openBridge : k1Target.status = .openBridge := rfl

theorem k1_not_proved : k1Target.status ≠ .provedProperty := by decide

end MCore
