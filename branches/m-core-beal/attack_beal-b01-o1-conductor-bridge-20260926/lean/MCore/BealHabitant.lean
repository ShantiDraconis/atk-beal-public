import MCore.K10
import MCore.BealF6Exclusion

namespace MCore

/-!
BEAL F6 — SINGLE HABITANT

The unique material inhabitant is not the equation itself and not an example.
It is the universal exclusion of the coprime case: every admissible exponential
solution forces a nontrivial common divisor of A,B,C.

This uses the repository's canonical CommonDivisor/CommonPrime vocabulary.
K10 already proves that these are equivalent.
-/

/-- Exact F6 inhabitant: every Beal datum has a nontrivial common divisor. -/
structure BealHabitant : Type where
  no_coprime :
    ∀ d : BealData,
      ∃ k : Nat, CommonDivisor k d.a d.b d.c

/-- The inhabitant closes the canonical Beal statement. -/
theorem beal_of_habitant
    (H : BealHabitant) :
    BealConjecture := by
  intro d
  exact commonPrime_iff_commonDivisor.mpr (H.no_coprime d)

/-- The frozen Beal theorem canonically yields the same inhabitant. -/
noncomputable def BealHabitant.ofBeal
    (h : BealConjecture) :
    BealHabitant :=
  { no_coprime := by
      intro d
      exact commonPrime_iff_commonDivisor.mp (h d) }

/-- Exact equivalence: inhabiting BealHabitant is neither weaker nor stronger
than proving the repository's frozen Beal statement. -/
theorem beal_iff_habitant :
    BealConjecture ↔ Nonempty BealHabitant := by
  constructor
  · intro h
    exact ⟨BealHabitant.ofBeal h⟩
  · rintro ⟨H⟩
    exact beal_of_habitant H

/-- A real Beal inhabitant produces the F6 exclusion certificate. -/
def BealHabitant.toExclusionCertificate
    (H : BealHabitant) :
    BealExclusionCertificate :=
  BealExclusionCertificate.ofBeal (beal_of_habitant H)

/-- Direct route into the unconditional claim certificate. -/
def BealHabitant.toUnconditionalClaim
    (H : BealHabitant) :
    BealUnconditionalClaimCertificate :=
  BealUnconditionalClaimCertificate.ofExclusion H.toExclusionCertificate

/-- Direct route into the final proof certificate. -/
def BealHabitant.toProofCertificate
    (H : BealHabitant) :
    BealProofCertificate :=
  H.toExclusionCertificate.toProofCertificate

/-- Single material producer type in the Beal F6 lane. -/
abbrev BealMaterialProducer : Type :=
  BealHabitant

#print axioms MCore.beal_of_habitant
#print axioms MCore.beal_iff_habitant
#print axioms MCore.BealHabitant.toExclusionCertificate
#print axioms MCore.BealHabitant.toUnconditionalClaim
#print axioms MCore.BealHabitant.toProofCertificate

end MCore
