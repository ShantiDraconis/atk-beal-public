import MCore.BealQuarticValuationPacket
import MCore.BealTwoSidedResolution

namespace MCore

/-- The concrete residual two-four family. -/
def T59TwoFourResidualExists : Prop :=
  ∃ d : T59ResidualCandidate,
    T51TwoFourPrime d.x d.y d.z

/--
Positive producer for the local two-four frontier:
every residual candidate in that family is impossible.
-/
structure TwoFourResidualEliminationProducer : Prop where
  eliminate :
    ∀ d : T59ResidualCandidate,
      T51TwoFourPrime d.x d.y d.z →
      False

/-- Negative producer for the local two-four frontier: one concrete survivor. -/
structure TwoFourResidualSurvivorProducer where
  candidate : T59ResidualCandidate
  family : T51TwoFourPrime candidate.x candidate.y candidate.z

theorem twoFourElimination_closes_local_positive
    (h : TwoFourResidualEliminationProducer) :
    ¬ T59TwoFourResidualExists := by
  rintro ⟨d, hd⟩
  exact h.eliminate d hd

theorem twoFourSurvivor_closes_local_negative
    (h : TwoFourResidualSurvivorProducer) :
    T59TwoFourResidualExists :=
  ⟨h.candidate, h.family⟩

/--
A concrete survivor of the two-four residual family is also a genuine Beal
counterexample, so the local negative route transports to the global negative
Beal endpoint.
-/
theorem twoFourSurvivor_refutes_beal
    (h : TwoFourResidualSurvivorProducer) :
    ¬ BealConjecture :=
  h.candidate.refutesBeal

/-- Exact bilateral resolution of the local two-four residual frontier. -/
def TwoFourResidualMateriallyResolved : Prop :=
  Nonempty TwoFourResidualEliminationProducer ∨
  Nonempty TwoFourResidualSurvivorProducer

theorem twoFourResidual_bilateral_outcome
    (h : TwoFourResidualMateriallyResolved) :
    (¬ T59TwoFourResidualExists) ∨ T59TwoFourResidualExists := by
  rcases h with hp | hn
  · rcases hp with ⟨p⟩
    exact Or.inl (twoFourElimination_closes_local_positive p)
  · rcases hn with ⟨n⟩
    exact Or.inr (twoFourSurvivor_closes_local_negative n)

theorem twoFourResidual_both_routes_contradict
    (hp : Nonempty TwoFourResidualEliminationProducer)
    (hn : Nonempty TwoFourResidualSurvivorProducer) :
    False := by
  rcases hp with ⟨p⟩
  rcases hn with ⟨n⟩
  exact (twoFourElimination_closes_local_positive p)
    (twoFourSurvivor_closes_local_negative n)

/--
Every residual candidate already carries the unconditional quartic valuation
packet.  For non-two-four families its quartic fields are vacuous implications;
for the two-four family they become concrete arithmetic constraints.
-/
theorem every_T59_has_quartic_valuation_packet
    (d : T59ResidualCandidate) :
    T59QuarticValuationPacket d :=
  T59_quartic_valuation_packet d

#print axioms MCore.twoFourElimination_closes_local_positive
#print axioms MCore.twoFourSurvivor_closes_local_negative
#print axioms MCore.twoFourSurvivor_refutes_beal
#print axioms MCore.twoFourResidual_bilateral_outcome
#print axioms MCore.twoFourResidual_both_routes_contradict
#print axioms MCore.every_T59_has_quartic_valuation_packet

end MCore
