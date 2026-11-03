import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

def AntiAllFour : Prop :=
  ∃ r : ReducedPrimitiveCandidate, AllFour r.x r.y r.z

def AntiEqualOddPrime : Prop :=
  ∃ r : ReducedPrimitiveCandidate, EqualOddPrime r.x r.y r.z

def AntiTwoFourPrime : Prop :=
  ∃ r : ReducedPrimitiveCandidate, TwoFourPrime r.x r.y r.z

def AntiOneFourEqual : Prop :=
  ∃ r : ReducedPrimitiveCandidate, OneFourEqualPrimes r.x r.y r.z

def AntiOneFourDistinct : Prop :=
  ∃ r : ReducedPrimitiveCandidate, OneFourDistinctPrimes r.x r.y r.z

def AntiTwoEqualOdd : Prop :=
  ∃ r : ReducedPrimitiveCandidate, TwoEqualOddPrimes r.x r.y r.z

def AntiThreeDistinctOdd : Prop :=
  ∃ r : ReducedPrimitiveCandidate, ThreeDistinctOddPrimes r.x r.y r.z

theorem allFour_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, AllFour r.x r.y r.z → False)
    (hNeg : AntiAllFour) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem equalOddPrime_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, EqualOddPrime r.x r.y r.z → False)
    (hNeg : AntiEqualOddPrime) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem twoFourPrime_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, TwoFourPrime r.x r.y r.z → False)
    (hNeg : AntiTwoFourPrime) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem oneFourEqual_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, OneFourEqualPrimes r.x r.y r.z → False)
    (hNeg : AntiOneFourEqual) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem oneFourDistinct_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, OneFourDistinctPrimes r.x r.y r.z → False)
    (hNeg : AntiOneFourDistinct) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem twoEqualOdd_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, TwoEqualOddPrimes r.x r.y r.z → False)
    (hNeg : AntiTwoEqualOdd) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

theorem threeDistinctOdd_inconsistent
    (hPos : ∀ r : ReducedPrimitiveCandidate, ThreeDistinctOddPrimes r.x r.y r.z → False)
    (hNeg : AntiThreeDistinctOdd) : False := by
  rcases hNeg with ⟨r, hr⟩
  exact hPos r hr

#print axioms MCore.BealEffective.OpenMath.allFour_inconsistent
#print axioms MCore.BealEffective.OpenMath.equalOddPrime_inconsistent
#print axioms MCore.BealEffective.OpenMath.twoFourPrime_inconsistent
#print axioms MCore.BealEffective.OpenMath.oneFourEqual_inconsistent
#print axioms MCore.BealEffective.OpenMath.oneFourDistinct_inconsistent
#print axioms MCore.BealEffective.OpenMath.twoEqualOdd_inconsistent
#print axioms MCore.BealEffective.OpenMath.threeDistinctOdd_inconsistent

end OpenMath
end BealEffective
end MCore
