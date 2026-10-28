import MCore.T60
import MCore.T36E_MASTER

namespace MCore

/-!
Post-T36E bridge: connect the frozen T60 candidate-level arithmetic packet
to the genuine Mathlib multiplicative-reduction theorem proved in T36E_MASTER.
This closes the minimal-model/multiplicative-reduction connection without
changing either frozen parent.
-/

theorem T60_packet_to_genuine_multiplicative_reduction
    (d : T59ResidualCandidate)
    {p : Nat}
    (h : T60OddLocalArithmeticPacket d p) :
    letI : (T36EMHeightOne p h.input.1).asIdeal.IsPrime :=
      (T36EMHeightOne p h.input.1).isPrime
    letI : IsDiscreteValuationRing (T36EMAtPrime p h.input.1) :=
      T36EM_atPrime_isDVR h.input.1
    (T36EMFreyCurve d.a d.b d.x d.y).HasMultiplicativeReduction
      (T36EMAtPrime p h.input.1) := by
  exact T36EM_hasMultiplicativeReduction d.equation h.input

def T60GenuineOddMultiplicativeReduction
    (d : T59ResidualCandidate) : Prop :=
  ∀ (p : Nat)
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z),
    let hpkt := T60_candidate_odd_prime_has_arithmetic_packet d hp hp2 hDelta
    letI : (T36EMHeightOne p hpkt.input.1).asIdeal.IsPrime :=
      (T36EMHeightOne p hpkt.input.1).isPrime
    letI : IsDiscreteValuationRing (T36EMAtPrime p hpkt.input.1) :=
      T36EM_atPrime_isDVR hpkt.input.1
    (T36EMFreyCurve d.a d.b d.x d.y).HasMultiplicativeReduction
      (T36EMAtPrime p hpkt.input.1)

theorem T60_every_candidate_has_genuine_odd_multiplicative_reduction
    (d : T59ResidualCandidate) :
    T60GenuineOddMultiplicativeReduction d := by
  intro p hp hp2 hDelta
  let hpkt := T60_candidate_odd_prime_has_arithmetic_packet d hp hp2 hDelta
  exact T60_packet_to_genuine_multiplicative_reduction d hpkt

/-- After this connection, the next scientific frontier is conductor
    exponent / exact lowered-level extraction from the genuine local reduction. -/
def PostT36EConductorState : T36GapState := .openBridge

#print axioms MCore.T60_packet_to_genuine_multiplicative_reduction
#print axioms MCore.T60_every_candidate_has_genuine_odd_multiplicative_reduction

end MCore
