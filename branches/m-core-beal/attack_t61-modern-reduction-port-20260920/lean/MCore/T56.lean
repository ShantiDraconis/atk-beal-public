import MCore.T55

namespace MCore

/-! T56 — elimination contract for the (p,p,q), p != q family. -/

def T56TwoEqualOddPrimesCase (c : T44LoweredNewformCase) : Prop :=
  T48AllPrime c.x c.y c.z ∧ T48ExactlyTwoEqual c.x c.y c.z

structure T56TwoEqualOddPrimesEliminationCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  eliminate :
    ∀ c : T44LoweredNewformCase,
      Survives c →
      T56TwoEqualOddPrimesCase c →
      False

theorem T56_certificate_eliminates
    {Survives : T44LoweredNewformCase → Prop}
    (cert : T56TwoEqualOddPrimesEliminationCertificate Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c)
    (hFamily : T56TwoEqualOddPrimesCase c) :
    False :=
  cert.eliminate c hSurvives hFamily

def T56TwoEqualOddPrimesState : T36GapState := .openBridge

#print axioms MCore.T56_certificate_eliminates

end MCore
