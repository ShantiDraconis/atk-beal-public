import MCore.B01ScientificInhabitant

namespace MCore

/-!
B01 DENSE SCIENTIFIC FRONTIER

This module does not add a Beal axiom and does not instantiate the open
mathematical objects.  It decomposes B01 into the smallest semantically
meaningful certificates that can be independently proved, audited, frozen,
and reused.
-/

/-- Exact p-adic exponent encoded without relying on an external factorization API. -/
def B01ExactPrimeExponent (p e N : Nat) : Prop :=
  p ^ e ∣ N ∧ ¬ p ^ (e + 1) ∣ N

/-- Prime divisor of the raw Frey discriminant. -/
def B01RawBadPrime (d : T59ResidualCandidate) (p : Nat) : Prop :=
  IsPrime p ∧
  p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z

/-- Odd bad prime; this is precisely the locus where T60 + T36E already
    provide genuine multiplicative reduction. -/
def B01OddBadPrime (d : T59ResidualCandidate) (p : Nat) : Prop :=
  B01RawBadPrime d p ∧ p ≠ 2

/-- Semantics of the genuine local conductor exponent.  `ActualExponent`
    must eventually be connected to a verified Artin/conductor definition;
    uniqueness prevents multiple incompatible exponents from being certified. -/
structure B01ConductorExponentSemantics where
  ActualExponent : T59ResidualCandidate → Nat → Nat → Prop
  unique :
    ∀ d p e₁ e₂,
      ActualExponent d p e₁ →
      ActualExponent d p e₂ →
      e₁ = e₂

/-- The exact theorem needed at every odd bad prime after the already-GREEN
    multiplicative-reduction prefix. -/
def B01OddExponentOneLaw
    (S : B01ConductorExponentSemantics) : Prop :=
  ∀ (d : T59ResidualCandidate) (p : Nat),
    B01OddBadPrime d p →
    S.ActualExponent d p 1

/-- Exact local contribution at p = 2.  No value is hard-coded. -/
structure B01TwoAdicExactPackage
    (S : B01ConductorExponentSemantics)
    (d : T59ResidualCandidate) where
  exponent : Nat
  actual : S.ActualExponent d 2 exponent

/-- Exact global conductor: every prime exponent is semantically certified
    and realized as the exact divisibility exponent of one positive integer. -/
structure B01GlobalConductorExactPackage
    (S : B01ConductorExponentSemantics)
    (d : T59ResidualCandidate)
    (two : B01TwoAdicExactPackage S d) where
  conductor : Nat
  positive : 0 < conductor
  localExponent : Nat → Nat
  localActual :
    ∀ (p : Nat), IsPrime p →
      S.ActualExponent d p (localExponent p)
  exactPrimePower :
    ∀ (p : Nat), IsPrime p →
      B01ExactPrimeExponent p (localExponent p) conductor
  twoExact : localExponent 2 = two.exponent
  oddOne :
    ∀ (p : Nat),
      IsPrime p →
      p ≠ 2 →
      p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z →
      localExponent p = 1

/-- Semantic interface for the residual representation and level-lowering
    theorem actually used by this route. -/
structure B01LevelLoweringSemantics where
  ResidualAdmissible : T59ResidualCandidate → Nat → Prop
  ActualLoweredLevel : T59ResidualCandidate → Nat → Nat → Prop
  lowered_unique :
    ∀ d ell N₁ N₂,
      ActualLoweredLevel d ell N₁ →
      ActualLoweredLevel d ell N₂ →
      N₁ = N₂

/-- A residual prime together with every semantic hypothesis required before
    level lowering is invoked.  `ResidualAdmissible` is deliberately not
    reduced to a Boolean proxy. -/
structure B01ResidualInput
    (L : B01LevelLoweringSemantics)
    (d : T59ResidualCandidate) where
  ell : Nat
  prime : IsPrime ell
  odd : ell ≠ 2
  admissible : L.ResidualAdmissible d ell

/-- Exact output of level lowering, tied simultaneously to the semantic
    theorem and to the already-certified structural B01 interface. -/
structure B01LoweredLevelExactPackage
    (L : B01LevelLoweringSemantics)
    (d : T59ResidualCandidate)
    (R : B01ResidualInput L d)
    (Nglobal : Nat) where
  level : Nat
  actual : L.ActualLoweredLevel d R.ell level
  positive : 0 < level
  dividesGlobalConductor : level ∣ Nglobal
  squarefree : B01Squarefree level
  support :
    ∀ q : Nat, IsPrime q → q ∣ level → q ∣ d.a * d.b * d.c

/-- Dense per-candidate B01 scientific inhabitant.

    This package contains no placeholder theorem fields: every field is an
    explicit mathematical object or proof that must be produced by the
    local-conductor / 2-adic / global-conductor / level-lowering analysis. -/
structure B01DenseScientificInhabitant
    (d : T59ResidualCandidate) where
  conductorSemantics : B01ConductorExponentSemantics
  oddExponentOne : B01OddExponentOneLaw conductorSemantics
  twoAdic : B01TwoAdicExactPackage conductorSemantics d
  global : B01GlobalConductorExactPackage conductorSemantics d twoAdic
  loweringSemantics : B01LevelLoweringSemantics
  residual : B01ResidualInput loweringSemantics d
  lowered :
    B01LoweredLevelExactPackage
      loweringSemantics d residual global.conductor

/-- Dense universal inhabitant: one genuine B01 package for every residual candidate. -/
structure B01DenseUniversal where
  inhabit : ∀ d : T59ResidualCandidate, B01DenseScientificInhabitant d

/-- Forgetful adapter from the dense semantics to the earlier semantic package. -/
def B01DenseScientificInhabitant.toScientific
    {d : T59ResidualCandidate}
    (H : B01DenseScientificInhabitant d) :
    B01ScientificInhabitant d :=
  let S : B01LocalConductorSemantics :=
    { ActualExponent := H.conductorSemantics.ActualExponent
      functional := H.conductorSemantics.unique }
  { semantics := S
    oddExponentOne := by
      intro d' p hp hp2 hDelta
      exact H.oddExponentOne d' p ⟨⟨hp, hDelta⟩, hp2⟩
    globalConductor :=
      { conductor := H.global.conductor
        positive := H.global.positive
        twoAdic :=
          { exponent := H.twoAdic.exponent
            actual := H.twoAdic.actual }
        oddExponent := H.global.localExponent
        oddActual := by
          intro p hp _hp2 _hDelta
          exact H.global.localActual p hp
        oddOne := H.global.oddOne }
    loweredLevel :=
      { level := H.lowered.level
        positive := H.lowered.positive
        dividesConductor := H.lowered.dividesGlobalConductor
        squarefree := H.lowered.squarefree
        support := H.lowered.support } }

/-- Dense B01 inhabitants are sufficient for the exact B01 certificate already
    consumed by the final mathematical chain. -/
def B01DenseScientificInhabitant.toExactCertificate
    {d : T59ResidualCandidate}
    (H : B01DenseScientificInhabitant d) :
    B01ExactConductorLevelCertificate d :=
  H.toScientific.toExactCertificate

def B01DenseUniversal.toExact
    (H : B01DenseUniversal) :
    ∀ d : T59ResidualCandidate, B01ExactConductorLevelCertificate d :=
  fun d => (H.inhabit d).toExactCertificate

/-- Already-GREEN input available to every dense B01 proof: genuine
    multiplicative reduction at every odd bad prime. -/
theorem b01_dense_green_prefix
    (d : T59ResidualCandidate) :
    T60GenuineOddMultiplicativeReduction d :=
  T60_every_candidate_has_genuine_odd_multiplicative_reduction d

/-- Dependency audit: after the GREEN multiplicative-reduction prefix, the
    odd local scientific delta is exactly the conductor-exponent-one law. -/
def B01OddScientificDelta
    (S : B01ConductorExponentSemantics) : Prop :=
  B01OddExponentOneLaw S

/-- The B01 dense frontier is intentionally data-valued and therefore cannot
    be inhabited by `True`, a marker Boolean, or a process certificate. -/
def B01DenseFrontier : Type :=
  B01DenseUniversal

#print axioms MCore.b01_dense_green_prefix

end MCore
