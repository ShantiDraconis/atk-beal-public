/-
T36E_TEMPLATE — integration target only.

Base snapshot:
  cd9d99990170e351e8c4b69bff4a60fc7580ffed

Important version boundary:
  that snapshot is pinned to Lean 4.19.0 and its lakefile has no Mathlib
  dependency. Mathlib v4.19.0 also predates
  Mathlib.AlgebraicGeometry.EllipticCurve.Reduction.

Therefore this file is intentionally NOT imported by MCore.lean on this branch.
It is the exact target template for the later Mathlib-enabled integration
branch where WeierstrassCurve.IsMinimal and HasMultiplicativeReduction exist.

Scientific purpose:
  E1: identify the canonical height-one valuation at (p) with the valuation
      consumed by the DVR Localization.AtPrime (p), at least on Delta and c4.
  E2: supply IsMinimal for the same Frey model over the same local DVR.
  E3: assemble those facts into the genuine Mathlib
      HasMultiplicativeReduction structure.

No endpoint promotion is encoded here.
-/

import MCore.T36
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Nat.Prime.Int

namespace MCore

open WeierstrassCurve
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- Convert the project's elementary prime predicate to Mathlib's Nat.Prime. -/
theorem T36E_natPrime_of_projectPrime
    {p : Nat} (hp : IsPrime p) :
    Nat.Prime p := by
  rw [Nat.prime_def]
  exact ⟨Nat.succ_le_of_lt hp.1, hp.2⟩

/-- The rational prime ideal (p) in Z. -/
def T36EPrimeIdeal (p : Nat) : Ideal ℤ :=
  Ideal.span {(p : ℤ)}

/-- The height-one point of Spec Z attached to the same project prime p. -/
noncomputable def T36EHeightOne
    (p : Nat) (hp : IsPrime p) :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := T36EPrimeIdeal p
  isPrime := by
    have hpNat : Nat.Prime p := T36E_natPrime_of_projectPrime hp
    unfold T36EPrimeIdeal
    exact (Ideal.span_singleton_prime
      (Int.ofNat_ne_zero.mpr hpNat.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hpNat)
  ne_bot := by
    have hpNat : Nat.Prime p := T36E_natPrime_of_projectPrime hp
    unfold T36EPrimeIdeal
    exact Ideal.span_singleton_eq_bot.not.mpr
      (Int.ofNat_ne_zero.mpr hpNat.ne_zero)

/-- The local DVR Z_(p). -/
abbrev T36EAtPrime
    (p : Nat) (hp : IsPrime p) : Type :=
  Localization.AtPrime (T36EHeightOne p hp).asIdeal

/-- E1 certificate.

The canonical valuation and the local-DVR valuation are required to agree on
exactly the two invariants consumed by multiplicative-reduction classification.
This avoids requiring global extensional equality of valuation functions. -/
structure T36ECanonicalAtPrimeCompatibility
    (p : Nat) (hp : IsPrime p)
    (W : WeierstrassCurve (FractionRing ℤ))
    [IsDiscreteValuationRing (T36EAtPrime p hp)] : Prop where
  deltaCanonical :
    (T36EHeightOne p hp).valuation (FractionRing ℤ) W.Δ < 1
  c4Canonical :
    (T36EHeightOne p hp).valuation (FractionRing ℤ) W.c₄ = 1
  deltaSame :
    (T36EHeightOne p hp).valuation (FractionRing ℤ) W.Δ =
      valuation (FractionRing ℤ)
        (IsLocalRing.maximalIdeal (T36EAtPrime p hp)) W.Δ
  c4Same :
    (T36EHeightOne p hp).valuation (FractionRing ℤ) W.c₄ =
      valuation (FractionRing ℤ)
        (IsLocalRing.maximalIdeal (T36EAtPrime p hp)) W.c₄

/-- E1 exports the bad-discriminant statement in the exact local valuation
used by Mathlib's reduction API. -/
theorem T36E_delta_local_of_compatibility
    {p : Nat} {hp : IsPrime p}
    {W : WeierstrassCurve (FractionRing ℤ)}
    [IsDiscreteValuationRing (T36EAtPrime p hp)]
    (h : T36ECanonicalAtPrimeCompatibility p hp W) :
    valuation (FractionRing ℤ)
      (IsLocalRing.maximalIdeal (T36EAtPrime p hp)) W.Δ < 1 := by
  rw [← h.deltaSame]
  exact h.deltaCanonical

/-- E1 exports the c4-unit statement in that same local valuation. -/
theorem T36E_c4_local_of_compatibility
    {p : Nat} {hp : IsPrime p}
    {W : WeierstrassCurve (FractionRing ℤ)}
    [IsDiscreteValuationRing (T36EAtPrime p hp)]
    (h : T36ECanonicalAtPrimeCompatibility p hp W) :
    valuation (FractionRing ℤ)
      (IsLocalRing.maximalIdeal (T36EAtPrime p hp)) W.c₄ = 1 := by
  rw [← h.c4Same]
  exact h.c4Canonical

/-- E2 certificate: the exact same Weierstrass model is minimal over Z_(p). -/
structure T36EMinimalityCertificate
    (p : Nat) (hp : IsPrime p)
    (W : WeierstrassCurve (FractionRing ℤ))
    [IsDiscreteValuationRing (T36EAtPrime p hp)] : Prop where
  minimal :
    WeierstrassCurve.IsMinimal (T36EAtPrime p hp) W

/-- Complete T36E bundle.  Possessing this bundle means the valuation adapter
and minimality have both been discharged for one and the same model W and
one and the same prime p. -/
structure T36ECompleteLocalBundle
    (p : Nat) (hp : IsPrime p)
    (W : WeierstrassCurve (FractionRing ℤ))
    [IsDiscreteValuationRing (T36EAtPrime p hp)] : Prop where
  compatibility : T36ECanonicalAtPrimeCompatibility p hp W
  minimality : T36EMinimalityCertificate p hp W

/-- E3 assembly theorem.

Once E1 and E2 are genuinely supplied, Mathlib's own reduction structure
closes immediately.  No separate Tate-algorithm proposition is inserted. -/
theorem T36E_bundle_to_hasMultiplicativeReduction
    {p : Nat} {hp : IsPrime p}
    {W : WeierstrassCurve (FractionRing ℤ)}
    [IsDiscreteValuationRing (T36EAtPrime p hp)]
    (b : T36ECompleteLocalBundle p hp W) :
    W.HasMultiplicativeReduction (T36EAtPrime p hp) := by
  letI : WeierstrassCurve.IsMinimal (T36EAtPrime p hp) W :=
    b.minimality.minimal
  exact {
    badReduction := T36E_delta_local_of_compatibility b.compatibility
    multiplicativeReduction := T36E_c4_local_of_compatibility b.compatibility
  }

/-- Fail-closed state carried by this template.

On the cd9d999 snapshot, these remain open because the required reduction API
is not present in the pinned dependency set. -/
structure T36ETemplateState where
  canonicalToAtPrime : T36GapState
  minimality : T36GapState
  multiplicativeReduction : T36GapState

def T36ECurrentTemplateState : T36ETemplateState where
  canonicalToAtPrime := .openBridge
  minimality := .openBridge
  multiplicativeReduction := .openBridge

#print axioms MCore.T36E_natPrime_of_projectPrime
#print axioms MCore.T36E_delta_local_of_compatibility
#print axioms MCore.T36E_c4_local_of_compatibility
#print axioms MCore.T36E_bundle_to_hasMultiplicativeReduction

end MCore
