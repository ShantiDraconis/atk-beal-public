import MCore.OpenMath.BealQ10SevenFamilies
import Mathlib.NumberTheory.FLT.Four

namespace MCore.OpenMath.BealQ10

def AllFourEliminated : Prop :=
  ∀ r : ReducedCandidate, AllFour r.x r.y r.z → False

def EqualOddPrimeEliminated : Prop :=
  ∀ r : ReducedCandidate, EqualOddPrime r.x r.y r.z → False

def TwoFourPrimeEliminated : Prop :=
  ∀ r : ReducedCandidate, TwoFourPrime r.x r.y r.z → False

def OneFourEqualPrimesEliminated : Prop :=
  ∀ r : ReducedCandidate, OneFourEqualPrimes r.x r.y r.z → False

def OneFourDistinctPrimesEliminated : Prop :=
  ∀ r : ReducedCandidate, OneFourDistinctPrimes r.x r.y r.z → False

def TwoEqualOddPrimesEliminated : Prop :=
  ∀ r : ReducedCandidate, TwoEqualOddPrimes r.x r.y r.z → False

def ThreeDistinctOddPrimesEliminated : Prop :=
  ∀ r : ReducedCandidate, ThreeDistinctOddPrimes r.x r.y r.z → False

theorem allFour_eliminated_mathlib : AllFourEliminated := by
  intro r h4
  rcases h4 with ⟨hx, hy, hz⟩
  have hne : r.a ^ 4 + r.b ^ 4 ≠ r.c ^ 4 :=
    fermatLastTheoremFour
      r.a r.b r.c
      (Nat.ne_of_gt r.a_pos)
      (Nat.ne_of_gt r.b_pos)
      (Nat.ne_of_gt r.c_pos)
  apply hne
  simpa [hx, hy, hz] using r.equation

/-- The exact residual OPEN_MATH after the all-four family is discharged. -/
structure SixFamilyMinCut : Prop where
  equalOddPrime : EqualOddPrimeEliminated
  twoFourPrime : TwoFourPrimeEliminated
  oneFourEqualPrimes : OneFourEqualPrimesEliminated
  oneFourDistinctPrimes : OneFourDistinctPrimesEliminated
  twoEqualOddPrimes : TwoEqualOddPrimesEliminated
  threeDistinctOddPrimes : ThreeDistinctOddPrimesEliminated

theorem SixFamilyMinCut.eliminates_seven
    (K : SixFamilyMinCut)
    (r : ReducedCandidate)
    (h : SevenFamilySplit r.x r.y r.z) :
    False := by
  rcases h with hA | h
  · exact allFour_eliminated_mathlib r hA
  rcases h with hB | h
  · exact K.equalOddPrime r hB
  rcases h with hC | h
  · exact K.twoFourPrime r hC
  rcases h with hD | h
  · exact K.oneFourEqualPrimes r hD
  rcases h with hE | h
  · exact K.oneFourDistinctPrimes r hE
  rcases h with hF | hG
  · exact K.twoEqualOddPrimes r hF
  · exact K.threeDistinctOddPrimes r hG

/-- Six material eliminators are sufficient for the full Q10 endpoint. -/
theorem sixFamilyMinCut_closes_Q10
    (K : SixFamilyMinCut) :
    MCore.OpenMath.BealProbe.MaterialPrimitiveExclusion := by
  intro d hd
  rcases primitive_seven_family d hd with ⟨r, hs⟩
  exact K.eliminates_seven r hs

#print axioms MCore.OpenMath.BealQ10.allFour_eliminated_mathlib
#print axioms MCore.OpenMath.BealQ10.sixFamilyMinCut_closes_Q10

end MCore.OpenMath.BealQ10
