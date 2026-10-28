import MCore.T56

namespace MCore

/-! T57 — elimination contract for pairwise-distinct odd-prime signatures. -/

def T57ThreeDistinctOddPrimesCase (c : T44LoweredNewformCase) : Prop :=
  T48AllPrime c.x c.y c.z ∧ T48AllDistinct c.x c.y c.z

structure T57ThreeDistinctOddPrimesEliminationCertificate
    (Survives : T44LoweredNewformCase → Prop) where
  eliminate :
    ∀ c : T44LoweredNewformCase,
      Survives c →
      T57ThreeDistinctOddPrimesCase c →
      False

theorem T57_certificate_eliminates
    {Survives : T44LoweredNewformCase → Prop}
    (cert : T57ThreeDistinctOddPrimesEliminationCertificate Survives)
    {c : T44LoweredNewformCase}
    (hSurvives : Survives c)
    (hFamily : T57ThreeDistinctOddPrimesCase c) :
    False :=
  cert.eliminate c hSurvives hFamily

def T57ThreeDistinctOddPrimesState : T36GapState := .openBridge

#print axioms MCore.T57_certificate_eliminates

end MCore
