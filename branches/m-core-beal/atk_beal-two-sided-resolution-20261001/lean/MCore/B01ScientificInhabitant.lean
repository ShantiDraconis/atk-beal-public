import MCore.PostT36EConductorBridge
import MCore.B01ExactConductorLevelCertificate

namespace MCore

/-- Semantic interface for a genuine local conductor exponent.  The predicate
    is intentionally abstract until a verified conductor formalization is connected. -/
structure B01LocalConductorSemantics where
  ActualExponent : T59ResidualCandidate → Nat → Nat → Prop
  functional :
    ∀ d p e₁ e₂, ActualExponent d p e₁ → ActualExponent d p e₂ → e₁ = e₂

/-- Exact odd-prime scientific theorem still required after genuine
    multiplicative reduction has already been proved. -/
def B01OddMultiplicativeExponentOne
    (S : B01LocalConductorSemantics) : Prop :=
  ∀ (d : T59ResidualCandidate) (p : Nat)
    (hp : IsPrime p) (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z),
    S.ActualExponent d p 1

/-- Exact p=2 contribution needed by the global conductor. -/
structure B01TwoAdicConductorPackage
    (S : B01LocalConductorSemantics) (d : T59ResidualCandidate) where
  exponent : Nat
  actual : S.ActualExponent d 2 exponent

/-- Global conductor assembled from genuine local exponents. -/
structure B01ActualGlobalConductorPackage
    (S : B01LocalConductorSemantics) (d : T59ResidualCandidate) where
  conductor : Nat
  positive : 0 < conductor
  twoAdic : B01TwoAdicConductorPackage S d
  oddExponent : Nat → Nat
  oddActual :
    ∀ (p : Nat), IsPrime p → p ≠ 2 →
      p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z →
      S.ActualExponent d p (oddExponent p)
  oddOne :
    ∀ (p : Nat), IsPrime p → p ≠ 2 →
      p ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z →
      oddExponent p = 1

/-- Exact level-lowering output attached to the genuine conductor package. -/
structure B01ActualLoweredLevelPackage
    (S : B01LocalConductorSemantics)
    (d : T59ResidualCandidate)
    (G : B01ActualGlobalConductorPackage S d) where
  level : Nat
  positive : 0 < level
  dividesConductor : level ∣ G.conductor
  squarefree : B01Squarefree level
  support :
    ∀ q : Nat, IsPrime q → q ∣ level → q ∣ d.a * d.b * d.c

/-- Genuine B01 scientific inhabitant, with semantics separated from bookkeeping. -/
structure B01ScientificInhabitant (d : T59ResidualCandidate) where
  semantics : B01LocalConductorSemantics
  oddExponentOne : B01OddMultiplicativeExponentOne semantics
  globalConductor : B01ActualGlobalConductorPackage semantics d
  loweredLevel : B01ActualLoweredLevelPackage semantics d globalConductor

/-- A genuine scientific inhabitant canonically fills the previously constructed
    B01 exact conductor/level certificate. -/
def B01ScientificInhabitant.toExactCertificate
    {d : T59ResidualCandidate}
    (H : B01ScientificInhabitant d) :
    B01ExactConductorLevelCertificate d where
  localExponent := fun _p =>
    { exponent := 1
      exact_one_of_multiplicative := by
        intro _
        rfl }
  globalConductor :=
    { conductor := H.globalConductor.conductor
      positive := H.globalConductor.positive
      twoAdicExponent := H.globalConductor.twoAdic.exponent
      oddExponent := H.globalConductor.oddExponent
      odd_exact := H.globalConductor.oddOne }
  loweredLevel :=
    { loweredLevel := H.loweredLevel.level
      positive := H.loweredLevel.positive
      dividesConductor := H.loweredLevel.dividesConductor
      squarefree := H.loweredLevel.squarefree
      support := H.loweredLevel.support }

/-- Universal B01 closure target.  This is data, not a proposition. -/
structure B01ScientificUniversal where
  inhabit : ∀ d : T59ResidualCandidate, B01ScientificInhabitant d

def B01ScientificUniversal.toExact
    (H : B01ScientificUniversal) :
    ∀ d : T59ResidualCandidate, B01ExactConductorLevelCertificate d :=
  fun d => (H.inhabit d).toExactCertificate

end MCore
