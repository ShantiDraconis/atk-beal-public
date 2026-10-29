import MCore.K6
namespace MCore
structure OfficialSpecFreeze where
  route : ResearchRoute
  statement_transcription : String
  status : SignatureStatus := .openBridge
def k7_officialSpec : OfficialSpecFreeze := { route := .commonPrime, statement_transcription := "If A^x + B^y = C^z for positive integers with x,y,z > 2, then A,B,C have a common prime factor.", status := .openBridge }
def k7_spec_node : CertNode := { status := k7_officialSpec.status, statement := True }
theorem k7_spec_status_openBridge : k7_spec_node.status = .openBridge := rfl
theorem k7_spec_not_proved : k7_spec_node.status ≠ .provedProperty := by decide
theorem k7_spec_not_certified : ¬ Nonempty (ProofCertificate k7_spec_node) := by intro h; rcases h with ⟨c⟩; exact k7_spec_not_proved c.status_proved
end MCore
