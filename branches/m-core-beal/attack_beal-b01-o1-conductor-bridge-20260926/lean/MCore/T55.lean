import MCore.T54

namespace MCore

/-! T55 — elimination contract for the (4,p,q), p != q family. -/

def T55OneFourDistinctPrimesCase (c : T44LoweredNewformCase) : Prop :=
  T51OneFourDistinctPrimes c.x c.y c.z

structure T55OneFourDistinctPrimesEliminationCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  eliminate :
    ∀ c : T44LoweredNewformCase,
      Survives c →
      T55OneFourDistinctPrimesCase c →
      False

theorem T55_certificate_eliminates
    {Survives : T44LoweredNewformCase → Prop}
    (cert : T55OneFourDistinctPrimesEliminationCertificate Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c)
    (hFamily : T55OneFourDistinctPrimesCase c) :
    False :=
  cert.eliminate c hSurvives hFamily

def T55OneFourDistinctPrimesState : T36GapState := .openBridge

#print axioms MCore.T55_certificate_eliminates

end MCore
