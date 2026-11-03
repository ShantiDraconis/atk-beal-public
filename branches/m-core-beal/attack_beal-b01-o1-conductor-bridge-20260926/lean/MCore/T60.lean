import MCore.T59

namespace MCore

/-!
T60 — CONCRETE ODD-PRIME LOCAL ARITHMETIC PACKET

For every concrete residual candidate and every odd prime dividing the raw
Frey discriminant, T33-T34 already prove the full arithmetic input currently
available before genuine elliptic reduction theory:
* prime / odd;
* divides the raw discriminant;
* does not divide the c4 kernel;
* lies in the support of exactly one base;
* gives exactly one nodal root collision.

T60 packages these facts at the candidate level used by T59.
-/

structure T60OddLocalArithmeticPacket
    (d : T59ResidualCandidate)
    (p : Nat) where
  input :
    T33OddPrimeReductionInput
      d.a d.b d.c d.x d.y d.z p
  nodal :
    T34FreyNodalCollision
      d.a d.b d.x d.y p

theorem T60_candidate_odd_prime_has_arithmetic_packet
    (d : T59ResidualCandidate)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hDelta :
      p ∣ T24FreyDiscriminantBeal
        d.a d.b d.c d.x d.y d.z) :
    T60OddLocalArithmeticPacket d p := by
  have hx0 : 0 < d.x :=
    Nat.lt_trans (by decide : 0 < 2) d.x_reduced.1
  have hy0 : 0 < d.y :=
    Nat.lt_trans (by decide : 0 < 2) d.y_reduced.1
  have hz0 : 0 < d.z :=
    Nat.lt_trans (by decide : 0 < 2) d.z_reduced.1
  have hInput :
      T33OddPrimeReductionInput
        d.a d.b d.c d.x d.y d.z p :=
    T33_odd_delta_prime_has_reduction_input
      hx0 hy0 hz0
      d.equation
      d.pairwisePrimitive
      hp hp2 hDelta
  refine ⟨hInput, ?_⟩
  exact T34_reduction_input_to_nodal_collision
    hx0 hy0 hz0
    d.equation
    d.pairwisePrimitive
    hInput

/-- Candidate-level closure of every odd raw-discriminant prime into the
    arithmetic packet. -/
def T60OddLocalArithmeticConstraint
    (d : T59ResidualCandidate) : Prop :=
  ∀ p : Nat,
    IsPrime p →
    p ≠ 2 →
    p ∣ T24FreyDiscriminantBeal
      d.a d.b d.c d.x d.y d.z →
    T60OddLocalArithmeticPacket d p

theorem T60_every_candidate_satisfies_odd_local_arithmetic
    (d : T59ResidualCandidate) :
    T60OddLocalArithmeticConstraint d := by
  intro p hp hp2 hDelta
  exact T60_candidate_odd_prime_has_arithmetic_packet
    d hp hp2 hDelta

/-- Direct extraction: every odd bad prime in the raw discriminant is already
    known not to divide the c4 kernel. -/
theorem T60_odd_bad_prime_not_dvd_c4
    (d : T59ResidualCandidate)
    {p : Nat}
    (h : T60OddLocalArithmeticPacket d p) :
    ¬ p ∣ T32FreyC4Kernel d.a d.b d.x d.y :=
  h.input.2.2.2.1

/-- Direct extraction: every such prime is supported on at least one of
    A,B,C; pairwise primitiveness plus T34 gives the exact-one collision. -/
theorem T60_odd_bad_prime_base_support
    (d : T59ResidualCandidate)
    {p : Nat}
    (h : T60OddLocalArithmeticPacket d p) :
    p ∣ d.a ∨ p ∣ d.b ∨ p ∣ d.c :=
  h.input.2.2.2.2

/-- T60 is algebraically closed.  The remaining transition is from this packet
    to genuine minimal-model / multiplicative-reduction / conductor data. -/
def T60OddReductionSemanticState : T36GapState :=
  .openBridge

#print axioms MCore.T60_candidate_odd_prime_has_arithmetic_packet
#print axioms MCore.T60_every_candidate_satisfies_odd_local_arithmetic
#print axioms MCore.T60_odd_bad_prime_not_dvd_c4
#print axioms MCore.T60_odd_bad_prime_base_support

end MCore
