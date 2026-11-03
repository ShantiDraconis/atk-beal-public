import MCore.PostT36EConductorBridge
import MCore.B01ConductorLevel

namespace MCore

/-- Exact local conductor exponent object used by the B01 frontier. -/
structure B01LocalConductorExponent
    (d : T59ResidualCandidate) (p : Nat) where
  exponent : Nat
  exact_one_of_multiplicative :
    T60OddLocalArithmeticPacket d p → exponent = 1

/-- Global conductor package with explicit 2-adic contribution and odd-prime exponents. -/
structure B01GlobalConductorPackage (d : T59ResidualCandidate) where
  conductor : Nat
  positive : 0 < conductor
  twoAdicExponent : Nat
  oddExponent : Nat → Nat
  odd_exact :
    ∀ (p : Nat), IsPrime p → p ≠ 2 →
      p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z →
      oddExponent p = 1

/-- Exact lowered level, with divisibility into the genuine global conductor. -/
structure B01LoweredLevelPackage (d : T59ResidualCandidate)
    (G : B01GlobalConductorPackage d) where
  loweredLevel : Nat
  positive : 0 < loweredLevel
  dividesConductor : loweredLevel ∣ G.conductor
  squarefree : B01Squarefree loweredLevel
  support :
    ∀ q : Nat, IsPrime q → q ∣ loweredLevel → q ∣ d.a * d.b * d.c

/--
Single dense B01 scientific obligation.
This is the exact object that must be inhabited before B01 may be promoted.
-/
structure B01ExactConductorLevelCertificate (d : T59ResidualCandidate) where
  localExponent : ∀ p : Nat, B01LocalConductorExponent d p
  globalConductor : B01GlobalConductorPackage d
  loweredLevel : B01LoweredLevelPackage d globalConductor

theorem b01_certificate_to_conductorLevel
    {d : T59ResidualCandidate}
    (C : B01ExactConductorLevelCertificate d) :
    B01ConductorLevel d C.loweredLevel.loweredLevel := by
  exact ⟨C.loweredLevel.positive, C.loweredLevel.squarefree, C.loweredLevel.support⟩

/-- Fail-closed frontier: there is currently no constructed certificate in this file. -/
def B01ExactConductorLevelState : T36GapState := .openBridge

#print axioms MCore.b01_certificate_to_conductorLevel

end MCore
