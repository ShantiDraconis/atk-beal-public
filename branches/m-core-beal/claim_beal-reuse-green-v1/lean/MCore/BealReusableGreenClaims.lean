import MCore.T58
import MCore.T60
import MCore.PostT36EConductorBridge
import MCore.B01ConductorLevel
import MCore.K10

namespace MCore

/-- Reused GREEN claim: candidate-level five-family signature coverage. -/
theorem beal_reuse_candidate_five_family
    (d : T59ResidualCandidate) :
    T51MixedFiveFamilySplit d.x d.y d.z :=
  T59_candidate_has_five_family_signature d

/-- Reused GREEN claim: every relevant odd discriminant prime has the concrete arithmetic packet. -/
theorem beal_reuse_odd_local_packet
    (d : T59ResidualCandidate)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z) :
    T60OddLocalArithmeticPacket d p :=
  T60_candidate_odd_prime_has_arithmetic_packet d hp hp2 hDelta

/-- Reused GREEN claim: every candidate satisfies the odd-local arithmetic constraint. -/
theorem beal_reuse_all_odd_local_arithmetic
    (d : T59ResidualCandidate) :
    T60OddLocalArithmeticConstraint d :=
  T60_every_candidate_satisfies_odd_local_arithmetic d

/-- Reused GREEN claim: the arithmetic packet reaches genuine Mathlib multiplicative reduction. -/
theorem beal_reuse_genuine_odd_multiplicative_reduction
    (d : T59ResidualCandidate) :
    T60GenuineOddMultiplicativeReduction d :=
  T60_every_candidate_has_genuine_odd_multiplicative_reduction d

/-- Reused GREEN conditional claim: five certified residual families eliminate all residual survivors. -/
theorem beal_reuse_five_family_elimination
    {Survives : T44LoweredNewformCase → Prop}
    (hDomain : T58ResidualSurvivorDomain Survives)
    (bundle : T58MixedEliminationBundle Survives) :
    T44AllNewformsEliminated Survives :=
  T58_five_family_bundle_eliminates_residual_survivors hDomain bundle

/-- Reused GREEN endpoint infrastructure: CommonPrime iff nontrivial common divisor. -/
theorem beal_reuse_commonPrime_iff_commonDivisor {a b c : Nat} :
    CommonPrime a b c ↔ ∃ d : Nat, CommonDivisor d a b c :=
  commonPrime_iff_commonDivisor

/-- Reused GREEN bookkeeping claim for any already-constructed B01 conductor level. -/
theorem beal_reuse_b01_prime_support
    {d : T59ResidualCandidate} {N q : Nat}
    (hN : B01ConductorLevel d N)
    (hq : IsPrime q)
    (hqN : q ∣ N) :
    q ∣ d.a * d.b * d.c :=
  hN.prime_support hq hqN

#print axioms MCore.beal_reuse_candidate_five_family
#print axioms MCore.beal_reuse_odd_local_packet
#print axioms MCore.beal_reuse_all_odd_local_arithmetic
#print axioms MCore.beal_reuse_genuine_odd_multiplicative_reduction
#print axioms MCore.beal_reuse_five_family_elimination
#print axioms MCore.beal_reuse_commonPrime_iff_commonDivisor
#print axioms MCore.beal_reuse_b01_prime_support

end MCore
