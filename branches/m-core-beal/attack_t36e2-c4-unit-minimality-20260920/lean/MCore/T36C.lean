import MCore.T36B
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Nat.Prime.Int

namespace MCore

open WeierstrassCurve

/-- The project's elementary prime predicate agrees in the needed direction
    with Mathlib's Nat.Prime. This is the bridge used by the local DVR layer. -/
theorem T36C_natPrime_of_projectPrime
    {p : Nat} (hp : IsPrime p) :
    Nat.Prime p := by
  rw [Nat.prime_def]
  exact ⟨Nat.succ_le_of_lt hp.1, hp.2⟩

/-- The prime ideal (p) of Z attached to the same natural prime used by T33/T34. -/
def T36CPrimeIdeal (p : Nat) : Ideal ℤ :=
  Ideal.span {(p : ℤ)}

/-- For a project-prime p, the ideal (p) in Z is a genuine prime ideal. -/
theorem T36C_primeIdeal_isPrime
    {p : Nat} (hp : IsPrime p) :
    (T36CPrimeIdeal p).IsPrime := by
  have hpNat : Nat.Prime p := T36C_natPrime_of_projectPrime hp
  unfold T36CPrimeIdeal
  exact (Ideal.span_singleton_prime
    (Int.ofNat_ne_zero.mpr hpNat.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hpNat)

/-- The local prime ideal is nonzero. -/
theorem T36C_primeIdeal_ne_bot
    {p : Nat} (hp : IsPrime p) :
    T36CPrimeIdeal p ≠ (⊥ : Ideal ℤ) := by
  have hpNat : Nat.Prime p := T36C_natPrime_of_projectPrime hp
  unfold T36CPrimeIdeal
  exact Ideal.span_singleton_eq_bot.not.mpr
    (Int.ofNat_ne_zero.mpr hpNat.ne_zero)

/-- Local ring at the rational prime p. -/
abbrev T36CLocalRing (p : Nat) : Type :=
  Localization.AtPrime (T36CPrimeIdeal p)

/-- The localization Z_(p) used by the Frey local analysis is a DVR.
    This is a real Mathlib theorem, not a project axiom. -/
theorem T36C_localization_isDVR
    {p : Nat} (hp : IsPrime p) :
    IsDiscreteValuationRing (T36CLocalRing p) := by
  letI : (T36CPrimeIdeal p).IsPrime :=
    T36C_primeIdeal_isPrime hp
  exact
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ℤ (T36C_primeIdeal_ne_bot hp) (T36CLocalRing p)

/-- Integral Frey model over Z. -/
def T36CFreyCurveZ (a b x y : Nat) : WeierstrassCurve ℤ :=
  let A : ℤ := (a ^ x : Nat)
  let B : ℤ := (b ^ y : Nat)
  ⟨0, B - A, 0, -(A * B), 0⟩

/-- The same Frey model over the canonical fraction field of Z. -/
noncomputable def T36CFreyCurveFrac
    (a b x y : Nat) : WeierstrassCurve (FractionRing ℤ) :=
  (T36CFreyCurveZ a b x y).baseChange (FractionRing ℤ)

/-- The Mathlib classification step itself is already closed:
    once the model is minimal and the two valuation statements hold,
    multiplicative reduction follows directly from the actual
    HasMultiplicativeReduction structure. -/
theorem T36C_hasMultiplicativeReduction_of_local_data
    {R K : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K}
    [WeierstrassCurve.IsMinimal R W]
    (hDelta :
      valuation K (IsLocalRing.maximalIdeal R) W.Δ < 1)
    (hc4 :
      valuation K (IsLocalRing.maximalIdeal R) W.c₄ = 1) :
    W.HasMultiplicativeReduction R := by
  exact {
    badReduction := hDelta
    multiplicativeReduction := hc4
  }

/-- The remaining local semantic data after T36C. No theorem is asserted here:
    this record only names the three facts that still have to be constructed
    for the actual Frey model at p. -/
structure T36CLocalData
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : Prop where
  minimal : WeierstrassCurve.IsMinimal R W
  deltaBad :
    valuation K (IsLocalRing.maximalIdeal R) W.Δ < 1
  c4Unit :
    valuation K (IsLocalRing.maximalIdeal R) W.c₄ = 1

/-- A complete T36C local-data object yields genuine Mathlib multiplicative
    reduction. The instance is extracted from data rather than assumed. -/
theorem T36C_localData_to_multiplicative
    {R K : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K}
    (h : T36CLocalData R K W) :
    W.HasMultiplicativeReduction R := by
  letI : WeierstrassCurve.IsMinimal R W := h.minimal
  exact T36C_hasMultiplicativeReduction_of_local_data
    h.deltaBad h.c4Unit

/-- Fail-closed status after this layer. -/
structure T36CLocalOpenBridges where
  minimality : T36GapState
  deltaDivisibilityToValuation : T36GapState
  c4NondivisibilityToValuation : T36GapState

def T36CCurrentOpenBridges : T36CLocalOpenBridges where
  minimality := .openBridge
  deltaDivisibilityToValuation := .openBridge
  c4NondivisibilityToValuation := .openBridge

#print axioms MCore.T36C_natPrime_of_projectPrime
#print axioms MCore.T36C_primeIdeal_isPrime
#print axioms MCore.T36C_primeIdeal_ne_bot
#print axioms MCore.T36C_localization_isDVR
#print axioms MCore.T36C_hasMultiplicativeReduction_of_local_data
#print axioms MCore.T36C_localData_to_multiplicative

end MCore
