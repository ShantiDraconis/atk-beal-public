import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/--
Fermat at one fixed exponent, stated only with the data already present in the
reduced Beal candidate.  This is a material mathematical proposition, not a
wrapper around Beal's conclusion.
-/
def FLTAt (n : Nat) : Prop :=
  ∀ a b c : Nat,
    0 < a →
    0 < b →
    0 < c →
    a ^ n + b ^ n = c ^ n →
    False

/-- The seven concrete family-elimination obligations. -/
def AllFourEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, AllFour r.x r.y r.z → False

def EqualOddPrimeEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, EqualOddPrime r.x r.y r.z → False

def TwoFourPrimeEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, TwoFourPrime r.x r.y r.z → False

def OneFourEqualPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, OneFourEqualPrimes r.x r.y r.z → False

def OneFourDistinctPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, OneFourDistinctPrimes r.x r.y r.z → False

def TwoEqualOddPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, TwoEqualOddPrimes r.x r.y r.z → False

def ThreeDistinctOddPrimesEliminated : Prop :=
  ∀ r : ReducedPrimitiveCandidate, ThreeDistinctOddPrimes r.x r.y r.z → False

/--
The all-four family is exactly discharged by FLT at exponent 4.
No coprimality hypothesis is needed here.
-/
theorem flt4_eliminates_allFour
    (hFLT4 : FLTAt 4) :
    AllFourEliminated := by
  intro r h4
  rcases h4 with ⟨hx, hy, hz⟩
  apply hFLT4 r.a r.b r.c r.a_pos r.b_pos r.c_pos
  simpa [hx, hy, hz] using r.equation

/--
Equal odd-prime signatures reduce pointwise to FLT at that same prime.
-/
theorem primeFLT_eliminates_equalOddPrime
    (hPrimeFLT : ∀ p : Nat, OddPrimeExponent p → FLTAt p) :
    EqualOddPrimeEliminated := by
  intro r hEq
  rcases hEq with ⟨p, hp, hx, hy, hz⟩
  apply hPrimeFLT p hp r.a r.b r.c r.a_pos r.b_pos r.c_pos
  simpa [hx, hy, hz] using r.equation

/--
The five genuinely mixed signatures, kept as five independent material fields.
Nothing here assumes the terminal gcd conclusion.
-/
structure MixedFamilyEliminator : Prop where
  twoFourPrime : TwoFourPrimeEliminated
  oneFourEqualPrimes : OneFourEqualPrimesEliminated
  oneFourDistinctPrimes : OneFourDistinctPrimesEliminated
  twoEqualOddPrimes : TwoEqualOddPrimesEliminated
  threeDistinctOddPrimes : ThreeDistinctOddPrimesEliminated

/--
Exact min-cut after the seven-family reduction:
  * FLT(4) kills (4,4,4);
  * prime-by-prime FLT kills (p,p,p);
  * MixedFamilyEliminator kills exactly the remaining five signatures.
-/
structure ReducedFamilyMinCut : Prop where
  flt4 : FLTAt 4
  primeFLT : ∀ p : Nat, OddPrimeExponent p → FLTAt p
  mixed : MixedFamilyEliminator

theorem ReducedFamilyMinCut.eliminates_seven
    (K : ReducedFamilyMinCut)
    (r : ReducedPrimitiveCandidate)
    (hSeven : SevenFamilySplit r.x r.y r.z) :
    False := by
  rcases hSeven with hA | hRest
  · exact flt4_eliminates_allFour K.flt4 r hA
  rcases hRest with hB | hRest
  · exact primeFLT_eliminates_equalOddPrime K.primeFLT r hB
  rcases hRest with hC | hRest
  · exact K.mixed.twoFourPrime r hC
  rcases hRest with hD | hRest
  · exact K.mixed.oneFourEqualPrimes r hD
  rcases hRest with hE | hRest
  · exact K.mixed.oneFourDistinctPrimes r hE
  rcases hRest with hF | hG
  · exact K.mixed.twoEqualOddPrimes r hF
  · exact K.mixed.threeDistinctOddPrimes r hG

/--
Terminal forcing theorem.  The only way this theorem can close is by supplying
the exact material min-cut above; the theorem itself contains no additional
mathematical assumption and introduces no terminal conclusion as a field.
-/
theorem minCut_closes_exact_remaining
    (K : ReducedFamilyMinCut) :
    ExactRemainingObligation := by
  intro d
  by_cases h : 1 < gcd3 d
  · exact h
  · rcases failed_lowerBound_seven_family d h with ⟨r, hSeven⟩
    exact False.elim (K.eliminates_seven r hSeven)

/-- The resulting endpoint is the already-frozen Beal endpoint. -/
theorem minCut_closes_beal
    (K : ReducedFamilyMinCut) :
    BealConjecture :=
  exact_remaining_closes_beal (minCut_closes_exact_remaining K)

#print axioms MCore.BealEffective.OpenMath.flt4_eliminates_allFour
#print axioms MCore.BealEffective.OpenMath.primeFLT_eliminates_equalOddPrime
#print axioms MCore.BealEffective.OpenMath.ReducedFamilyMinCut.eliminates_seven
#print axioms MCore.BealEffective.OpenMath.minCut_closes_exact_remaining
#print axioms MCore.BealEffective.OpenMath.minCut_closes_beal

end OpenMath
end BealEffective
end MCore
