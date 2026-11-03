import MCore.BealUnconditionalClaimCertificate

namespace MCore

/-!
BEAL F6 — EXCLUSION TERMINAL

The Beal terminal shape is F6 (EXCLUSION), not F1 (VANISHING).
The bad space is represented canonically by BealData together with the
repository's exact counterexample predicate, avoiding any weakening through
an alternate gcd encoding.
-/

/-- Canonical bad-point predicate: an admissible Beal datum with no common
prime divisor. -/
def BealBadPoint (d : BealData) : Prop :=
  BealCounterexample d

/-- Exact bad space as a subtype. -/
def BealXBad : Type :=
  { d : BealData // BealBadPoint d }

/-- F6 terminal statement: the bad space has no inhabitant. -/
def BealExclusion : Prop :=
  ∀ x : BealXBad, False

/-- The unique material producer for the F6 lane. -/
structure BealExclusionCertificate : Type where
  exclude : BealExclusion

/-- Beal immediately gives exclusion of every bad point. -/
def BealExclusionCertificate.ofBeal
    (h : BealConjecture) :
    BealExclusionCertificate :=
  { exclude := by
      intro x
      exact x.2 (h x.1) }

/-- F6 exclusion is sufficient to recover the unconditional Beal theorem.
Classical excluded-middle is used only to convert absence of a counterexample
into the positive CommonPrime witness proposition. -/
theorem beal_of_exclusion
    (C : BealExclusionCertificate) :
    BealConjecture := by
  intro d
  by_contra h
  exact C.exclude ⟨d, h⟩

/-- Exact equivalence of the F6 terminal and the frozen Beal statement. -/
theorem beal_iff_exclusion_certificate :
    BealConjecture ↔ Nonempty BealExclusionCertificate := by
  constructor
  · intro h
    exact ⟨BealExclusionCertificate.ofBeal h⟩
  · rintro ⟨C⟩
    exact beal_of_exclusion C

/-- F6 certificate -> unconditional claim certificate. -/
def BealUnconditionalClaimCertificate.ofExclusion
    (C : BealExclusionCertificate) :
    BealUnconditionalClaimCertificate :=
  ⟨beal_of_exclusion C⟩

/-- F6 certificate -> kernel proof certificate. -/
def BealExclusionCertificate.toProofCertificate
    (C : BealExclusionCertificate) :
    BealProofCertificate :=
  (BealUnconditionalClaimCertificate.ofExclusion C).toProofCertificate

/-- Single material producer type for the Beal F6 lane. -/
abbrev OpenMathProducerBeal : Type :=
  BealExclusionCertificate

#print axioms MCore.beal_of_exclusion
#print axioms MCore.beal_iff_exclusion_certificate
#print axioms MCore.BealUnconditionalClaimCertificate.ofExclusion
#print axioms MCore.BealExclusionCertificate.toProofCertificate

end MCore
