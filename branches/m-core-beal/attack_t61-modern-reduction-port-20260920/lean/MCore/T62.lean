import MCore.T61
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.Dvr

namespace MCore

/-!
T62 — PRIME PLACE / DVR / MINIMALITY INFRASTRUCTURE

This module provides the exact local infrastructure needed to turn T60's
odd-prime arithmetic packet into Mathlib reduction data.

The minimality proof below follows the unit-c4 criterion used in the
Apache-2.0 FLT formalization (Fermat.FLT.Mathlib.AlgebraicGeometry.
EllipticCurve.Reduction), itself the v(c4)=0 special case of the
Kraus–Laska / Silverman minimality criterion.
-/

open IsDedekindDomain
open NumberField
open WeierstrassCurve

/-- Mathlib primality implies the elementary project-local primality notion. -/
theorem T62_natPrime_to_corePrime
    {p : Nat}
    (hp : Nat.Prime p) :
    MCore.IsPrime p := by
  refine ⟨hp.one_lt, ?_⟩
  intro d hd
  exact (Nat.dvd_prime hp).mp hd

/-- The height-one place of Q corresponding to a natural prime p, using
    Mathlib's native equivalence. -/
noncomputable def T62PrimePlace
    (p : Nat)
    (hp : Nat.Prime p) :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    (⟨p, hp⟩ : Nat.Primes)

/-- The native place recovers the original natural prime. -/
theorem T62_primePlace_natGenerator
    (p : Nat)
    (hp : Nat.Prime p) :
    Rat.HeightOneSpectrum.natGenerator (T62PrimePlace p hp) = p := by
  change
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
      (T62PrimePlace p hp)).1 = p
  rw [T62PrimePlace, Equiv.apply_symm_apply]

/-- The local ring at a finite prime of Q. -/
abbrev T62LocalRing
    (p : Nat)
    (hp : Nat.Prime p) :=
  Localization.AtPrime (T62PrimePlace p hp).asIdeal

/-- Algebra structure from the local ring into Q. -/
noncomputable instance T62_instAlgebraLocalRingRat
    (p : Nat)
    (hp : Nat.Prime p) :
    Algebra (T62LocalRing p hp) ℚ :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (T62LocalRing p hp) ℚ
    (T62PrimePlace p hp).asIdeal.primeCompl
    (nonZeroDivisors _)
    (T62PrimePlace p hp).asIdeal.primeCompl_le_nonZeroDivisors

/-- Compatibility of O_Q -> localization -> Q. -/
instance T62_instScalarTowerLocalRingRat
    (p : Nat)
    (hp : Nat.Prime p) :
    IsScalarTower (𝓞 ℚ) (T62LocalRing p hp) ℚ :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (T62LocalRing p hp) ℚ
    (T62PrimePlace p hp).asIdeal.primeCompl
    (nonZeroDivisors _)
    (T62PrimePlace p hp).asIdeal.primeCompl_le_nonZeroDivisors

/-- Q is the fraction field of the localized ring. -/
instance T62_instFractionRingLocalRingRat
    (p : Nat)
    (hp : Nat.Prime p) :
    IsFractionRing (T62LocalRing p hp) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (T62PrimePlace p hp).asIdeal.primeCompl
    (T62LocalRing p hp) ℚ

/-- The localization at a nonzero prime of the Dedekind domain O_Q is a DVR. -/
instance T62_instDVRLocalRingRat
    (p : Nat)
    (hp : Nat.Prime p) :
    IsDiscreteValuationRing (T62LocalRing p hp) := by
  haveI hdom : IsDomain (𝓞 ℚ) := inferInstance
  exact
    @IsDedekindDomainDvr.is_dvr_at_nonzero_prime
      (𝓞 ℚ) _ hdom _
      (T62PrimePlace p hp).asIdeal
      (T62PrimePlace p hp).ne_bot
      (T62PrimePlace p hp).isPrime

/-- Unit-c4 minimality criterion.

If an integral Weierstrass equation over a DVR has field-level c4 valuation
equal to 1 (multiplicative notation: c4 is a unit), then it is minimal.
-/
theorem T62_isMinimal_of_valuation_c4_eq_one
    {R K : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K)
    [IsIntegral R W]
    (hc4 :
      IsDedekindDomain.HeightOneSpectrum.valuation K
        (IsDiscreteValuationRing.maximalIdeal R) W.c₄ = 1) :
    IsMinimal R W := by
  open IsDiscreteValuationRing
    IsDedekindDomain.HeightOneSpectrum
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [
    one_smul,
    ← Subtype.coe_le_coe,
    valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W
  ]
  have hint :
      valuation K (maximalIdeal R) (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using
      valuation_le_one (maximalIdeal R)
        (integralModel R (C • W)).c₄
  rw [
    variableChange_c₄,
    map_mul,
    map_pow,
    hc4,
    mul_one
  ] at hint
  simpa [
    variableChange_Δ,
    map_mul,
    map_pow
  ] using
    mul_le_of_le_one_left'
      (pow_le_one'
        ((pow_le_one_iff (by norm_num)).mp hint) 12)

/-- The rational Frey model is integral over every finite-prime localization,
    because it is obtained by base change from an integral Z-model. -/
theorem T62_freyCurveQ_isIntegral
    (a b x y p : Nat)
    (hp : Nat.Prime p) :
    WeierstrassCurve.IsIntegral
      (T62LocalRing p hp)
      (T61FreyCurveQ a b x y) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift
    (T62LocalRing p hp)
  all_goals
    refine ⟨_, ?_⟩
  all_goals
    simp [T61FreyCurveQ, T61FreyCurveZ]

#print axioms MCore.T62_natPrime_to_corePrime
#print axioms MCore.T62_primePlace_natGenerator
#print axioms MCore.T62_isMinimal_of_valuation_c4_eq_one
#print axioms MCore.T62_freyCurveQ_isIntegral

end MCore
