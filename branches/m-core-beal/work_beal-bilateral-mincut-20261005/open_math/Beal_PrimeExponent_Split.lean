import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- The elementary project-prime predicate excludes 4. -/
theorem projectPrime_ne_four
    {p : Nat}
    (hp : IsPrime p) :
    p ≠ 4 := by
  intro hp4
  subst p
  have htwo : 2 ∣ (4 : Nat) := by decide
  rcases hp.2 2 htwo with h1 | h4
  · omega
  · omega

/--
Every reduced odd-prime exponent is either exactly 3 or at least 5.
This isolates the FLT(3) branch from the genuinely large-prime branch.
-/
theorem oddPrimeExponent_three_or_ge_five
    {p : Nat}
    (hp : OddPrimeExponent p) :
    p = 3 ∨ 5 ≤ p := by
  by_cases h3 : p = 3
  · exact Or.inl h3
  · right
    have h4 : p ≠ 4 := projectPrime_ne_four hp.1
    omega

/--
A reduced exponent has exactly three regimes:
  4, prime 3, or prime >= 5.
-/
theorem reducedExponent_trichotomy
    {r : Nat}
    (hr : ReducedExponent r) :
    r = 4 ∨ r = 3 ∨ (IsPrime r ∧ 5 ≤ r) := by
  rcases hr.2 with h4 | hp
  · exact Or.inl h4
  ·
    have hop : OddPrimeExponent r := ⟨hp, hr.1⟩
    rcases oddPrimeExponent_three_or_ge_five hop with h3 | h5
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr ⟨hp, h5⟩)

/--
Consequently every reduced candidate has a 3-way regime at each exponent.
This is pure finite pressure, not a new hypothesis.
-/
theorem reducedCandidate_exponent_regimes
    (r : ReducedPrimitiveCandidate) :
    (r.x = 4 ∨ r.x = 3 ∨ (IsPrime r.x ∧ 5 ≤ r.x)) ∧
    (r.y = 4 ∨ r.y = 3 ∨ (IsPrime r.y ∧ 5 ≤ r.y)) ∧
    (r.z = 4 ∨ r.z = 3 ∨ (IsPrime r.z ∧ 5 ≤ r.z)) := by
  exact ⟨
    reducedExponent_trichotomy r.x_reduced,
    reducedExponent_trichotomy r.y_reduced,
    reducedExponent_trichotomy r.z_reduced
  ⟩

#print axioms MCore.BealEffective.OpenMath.projectPrime_ne_four
#print axioms MCore.BealEffective.OpenMath.oddPrimeExponent_three_or_ge_five
#print axioms MCore.BealEffective.OpenMath.reducedExponent_trichotomy
#print axioms MCore.BealEffective.OpenMath.reducedCandidate_exponent_regimes

end OpenMath
end BealEffective
end MCore
