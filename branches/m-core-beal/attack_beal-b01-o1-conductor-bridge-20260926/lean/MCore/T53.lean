import MCore.T52

namespace MCore

/-! T53 — elimination contract for the (4,4,p) family, up to permutation. -/

def T53TwoFourPrimeCase (c : T44LoweredNewformCase) : Prop :=
  T51TwoFourPrime c.x c.y c.z

structure T53TwoFourPrimeEliminationCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  eliminate :
    ∀ c : T44LoweredNewformCase,
      Survives c →
      T53TwoFourPrimeCase c →
      False

theorem T53_certificate_eliminates
    {Survives : T44LoweredNewformCase → Prop}
    (cert : T53TwoFourPrimeEliminationCertificate Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c)
    (hFamily : T53TwoFourPrimeCase c) :
    False :=
  cert.eliminate c hSurvives hFamily

def T53TwoFourPrimeState : T36GapState := .openBridge

#print axioms MCore.T53_certificate_eliminates

end MCore
