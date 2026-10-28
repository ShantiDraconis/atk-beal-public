import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-
ATK forcing harness.
This file intentionally contains no closure theorem and no new mathematical
hypothesis. It exposes the exact seven-family questions the kernel must answer.
-/

/-- Q1: all exponents four. Exact eliminator required. -/
def ATK_Q1_AllFour : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    AllFour r.x r.y r.z → False

/-- Q2: all exponents the same odd prime. Exact eliminator required. -/
def ATK_Q2_EqualOddPrime : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    EqualOddPrime r.x r.y r.z → False

/-- Q3: exactly two exponents four. -/
def ATK_Q3_TwoFourPrime : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    TwoFourPrime r.x r.y r.z → False

/-- Q4: one exponent four, the other two equal odd primes. -/
def ATK_Q4_OneFourEqual : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    OneFourEqualPrimes r.x r.y r.z → False

/-- Q5: one exponent four, the other two distinct odd primes. -/
def ATK_Q5_OneFourDistinct : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    OneFourDistinctPrimes r.x r.y r.z → False

/-- Q6: two equal odd prime exponents, third distinct. -/
def ATK_Q6_TwoEqualOdd : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    TwoEqualOddPrimes r.x r.y r.z → False

/-- Q7: three distinct odd prime exponents. -/
def ATK_Q7_ThreeDistinctOdd : Prop :=
  ∀ r : ReducedPrimitiveCandidate,
    ThreeDistinctOddPrimes r.x r.y r.z → False

/-- Exact aggregation: answering all seven ATK questions eliminates every reduced candidate. -/
theorem ATK_all_seven_eliminate_reduced
    (q1 : ATK_Q1_AllFour)
    (q2 : ATK_Q2_EqualOddPrime)
    (q3 : ATK_Q3_TwoFourPrime)
    (q4 : ATK_Q4_OneFourEqual)
    (q5 : ATK_Q5_OneFourDistinct)
    (q6 : ATK_Q6_TwoEqualOdd)
    (q7 : ATK_Q7_ThreeDistinctOdd) :
    ∀ r : ReducedPrimitiveCandidate, False := by
  intro r
  have hs := reduced_signature_seven_family
    r.x_reduced r.y_reduced r.z_reduced
  rcases hs with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact q1 r h1
  · exact q2 r h2
  · exact q3 r h3
  · exact q4 r h4
  · exact q5 r h5
  · exact q6 r h6
  · exact q7 r h7

/-- If every reduced candidate is eliminated, the exact terminal obligation follows. -/
theorem ATK_no_reduced_closes_exact_remaining
    (hNoReduced : ∀ r : ReducedPrimitiveCandidate, False) :
    ExactRemainingObligation := by
  intro d
  rcases Nat.lt_or_ge 1 (gcd3 d) with hgood | hle
  · exact hgood
  · have hFail : ¬ 1 < gcd3 d := by
      intro hlt
      exact (Nat.not_le_of_gt hlt) hle
    rcases failed_lowerBound_to_reduced d hFail with ⟨r⟩
    exact False.elim (hNoReduced r)

/-- Full exact reduction of Beal to the seven ATK answers. -/
theorem ATK_all_answers_close_beal
    (q1 : ATK_Q1_AllFour)
    (q2 : ATK_Q2_EqualOddPrime)
    (q3 : ATK_Q3_TwoFourPrime)
    (q4 : ATK_Q4_OneFourEqual)
    (q5 : ATK_Q5_OneFourDistinct)
    (q6 : ATK_Q6_TwoEqualOdd)
    (q7 : ATK_Q7_ThreeDistinctOdd) :
    BealConjecture := by
  apply exact_remaining_closes_beal
  exact ATK_no_reduced_closes_exact_remaining
    (ATK_all_seven_eliminate_reduced q1 q2 q3 q4 q5 q6 q7)

#print axioms MCore.BealEffective.OpenMath.ATK_all_seven_eliminate_reduced
#print axioms MCore.BealEffective.OpenMath.ATK_no_reduced_closes_exact_remaining
#print axioms MCore.BealEffective.OpenMath.ATK_all_answers_close_beal

end OpenMath
end BealEffective
end MCore
