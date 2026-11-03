import MCore.T35

namespace MCore

/-- Fail-closed certificate for the odd-prime local-reduction bridge.
    Possessing this object means the exact T34 -> oddLocalReduction implication
    has been supplied; T36 does not manufacture that implication. -/
structure T36OddLocalReductionCertificate (G : T35GapLedger) where
  bridge : T35OddLocalReductionBridge G

theorem T36_certificate_discharges_odd_local
    {G : T35GapLedger}
    (c : T36OddLocalReductionCertificate G) :
    T35OddLocalReductionBridge G :=
  c.bridge

/-- Explicit scientific state at this checkpoint. -/
inductive T36GapState
  | openBridge
  | certified

def T36OddLocalReductionState : T36GapState :=
  .openBridge

#print axioms MCore.T36_certificate_discharges_odd_local

end MCore
