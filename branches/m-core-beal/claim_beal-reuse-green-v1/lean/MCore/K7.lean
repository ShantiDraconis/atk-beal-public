import MCore.K6
import MCore.BealSpecification

namespace MCore

/-- K7 binds the certification firewall to the actual Beal proposition. -/
def bealEndpointNode : CertNode :=
  { status := .openBridge
    statement := BealConjecture }

theorem k7_endpoint_status_open : bealEndpointNode.status = .openBridge := rfl

theorem k7_endpoint_not_proved : bealEndpointNode.status ≠ .provedProperty := by
  decide

theorem k7_endpoint_not_certified :
    ¬ Nonempty (ProofCertificate bealEndpointNode) := by
  intro h
  rcases h with ⟨c⟩
  exact k7_endpoint_not_proved c.status_proved

/-- A genuine proof can be packaged only after it is supplied explicitly. -/
def provedBealNode : CertNode :=
  { status := .provedProperty
    statement := BealConjecture }

def certifyBeal (h : BealConjecture) : ProofCertificate provedBealNode :=
  { status_proved := rfl
    proof := h }

end MCore
