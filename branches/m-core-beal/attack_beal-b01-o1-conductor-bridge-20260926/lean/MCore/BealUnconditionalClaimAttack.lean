import MCore.BealUnconditionalClaimCertificate
import MCore.T34

namespace MCore

/-!
Exact unconditional Beal attack frontier.

This file removes all remaining routing ambiguity: the positive theorem is
enabled exactly by refuting the canonical T34 residual candidate.  No status
flag, B01/B02 infrastructure certificate, or route marker can inhabit this
obligation.
-/

/-- Single irreducible mathematical obligation for unconditional closure. -/
abbrev BealUnconditionalKernelObligation : Prop :=
  ¬ T34FreyNodalCollisionCandidate

/-- Exact equivalence to the frozen Beal theorem. -/
theorem beal_iff_unconditional_kernel_obligation :
    BealConjecture ↔ BealUnconditionalKernelObligation :=
  T34_beal_iff_nodal_collision_frontier

/-- A proof of the exact kernel obligation creates the unconditional claim. -/
def BealUnconditionalClaimCertificate.ofKernelObligation
    (h : BealUnconditionalKernelObligation) :
    BealUnconditionalClaimCertificate :=
  ⟨beal_iff_unconditional_kernel_obligation.mpr h⟩

/-- Exact direct theorem enablement from the irreducible obligation. -/
theorem enable_beal_from_unconditional_kernel_obligation
    (h : BealUnconditionalKernelObligation) :
    BealConjecture :=
  (BealUnconditionalClaimCertificate.ofKernelObligation h).enableTheorem

/-- Exact direct proof-certificate issuance. -/
def issue_beal_proof_certificate_from_kernel_obligation
    (h : BealUnconditionalKernelObligation) :
    BealProofCertificate :=
  (BealUnconditionalClaimCertificate.ofKernelObligation h).toProofCertificate

/-- The obligation is not an auxiliary assumption: any Beal proof returns it. -/
theorem unconditional_kernel_obligation_of_beal
    (h : BealConjecture) :
    BealUnconditionalKernelObligation :=
  beal_iff_unconditional_kernel_obligation.mp h

#print axioms MCore.beal_iff_unconditional_kernel_obligation
#print axioms MCore.enable_beal_from_unconditional_kernel_obligation
#print axioms MCore.issue_beal_proof_certificate_from_kernel_obligation
#print axioms MCore.unconditional_kernel_obligation_of_beal

end MCore
