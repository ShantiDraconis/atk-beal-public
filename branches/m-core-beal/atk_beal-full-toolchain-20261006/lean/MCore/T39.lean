import MCore.T38

namespace MCore

/-- Fail-closed certificate for the modularity interface actually required by
    the Frey object produced by this chain. -/
structure T39ModularityCertificate (G : T35GapLedger) where
  bridge : T35ModularityBridge G

theorem T39_certificate_discharges_modularity
    {G : T35GapLedger}
    (c : T39ModularityCertificate G) :
    T35ModularityBridge G :=
  c.bridge

def T39ModularityState : T36GapState :=
  .openBridge

#print axioms MCore.T39_certificate_discharges_modularity

end MCore
