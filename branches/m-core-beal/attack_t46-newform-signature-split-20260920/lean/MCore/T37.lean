import MCore.T36

namespace MCore

/-- Fail-closed certificate for the p=2 local-reduction bridge. -/
structure T37TwoAdicReductionCertificate (G : T35GapLedger) where
  bridge : T35TwoAdicReductionBridge G

theorem T37_certificate_discharges_two_adic
    {G : T35GapLedger}
    (c : T37TwoAdicReductionCertificate G) :
    T35TwoAdicReductionBridge G :=
  c.bridge

def T37TwoAdicReductionState : T36GapState :=
  .openBridge

#print axioms MCore.T37_certificate_discharges_two_adic

end MCore
