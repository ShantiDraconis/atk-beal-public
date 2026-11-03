import MCore.T53

namespace MCore

/-! T54 — elimination contract for the (4,p,p) family, up to permutation. -/

def T54OneFourEqualPrimesCase (c : T44LoweredNewformCase) : Prop :=
  T51OneFourEqualPrimes c.x c.y c.z

structure T54OneFourEqualPrimesEliminationCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  eliminate :
    ∀ c : T44LoweredNewformCase,
      Survives c →
      T54OneFourEqualPrimesCase c →
      False

theorem T54_certificate_eliminates
    {Survives : T44LoweredNewformCase → Prop}
    (cert : T54OneFourEqualPrimesEliminationCertificate Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c)
    (hFamily : T54OneFourEqualPrimesCase c) :
    False :=
  cert.eliminate c hSurvives hFamily

def T54OneFourEqualPrimesState : T36GapState := .openBridge

#print axioms MCore.T54_certificate_eliminates

end MCore
