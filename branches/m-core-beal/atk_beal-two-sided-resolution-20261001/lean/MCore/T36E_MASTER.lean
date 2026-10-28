import MCore.T33
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

namespace MCore

open WeierstrassCurve
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open IsDiscreteValuationRing

/-!
T36E_MASTER

Executable Mathlib-master attack for the odd-prime local Frey bridge.

The frozen T36E_TEMPLATE remains unchanged.  This file proves the exact
predicates consumed by HasMultiplicativeReduction:

* canonical p-adic and AtPrime-DVR valuations have the same < 1 test on
  embedded naturals;
* they have the same = 1 test on embedded naturals;
* T33's p | Delta and p ∤ c4 give those local-DVR facts for the same Frey model;
* c4-unit + integrality forces that same model to be minimal;
* Mathlib's genuine HasMultiplicativeReduction structure follows.

No conductor-exponent theorem is asserted here.
-/

/-- Project prime -> Mathlib prime. -/
theorem T36EM_natPrime_of_projectPrime
    {p : Nat} (hp : IsPrime p) :
    Nat.Prime p := by
  rw [Nat.prime_def]
  exact ⟨Nat.succ_le_of_lt hp.1, hp.2⟩

/-- The rational prime ideal (p) in Z. -/
def T36EMPrimeIdeal (p : Nat) : Ideal ℤ :=
  Ideal.span {(p : ℤ)}

/-- The corresponding height-one point of Spec Z. -/
noncomputable def T36EMHeightOne
    (p : Nat) (hp : IsPrime p) :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := T36EMPrimeIdeal p
  isPrime := by
    have hpNat : Nat.Prime p := T36EM_natPrime_of_projectPrime hp
    unfold T36EMPrimeIdeal
    exact (Ideal.span_singleton_prime
      (Int.ofNat_ne_zero.mpr hpNat.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hpNat)
  ne_bot := by
    have hpNat : Nat.Prime p := T36EM_natPrime_of_projectPrime hp
    unfold T36EMPrimeIdeal
    exact Ideal.span_singleton_eq_bot.not.mpr
      (Int.ofNat_ne_zero.mpr hpNat.ne_zero)

/-- The local ring Z_(p). -/
abbrev T36EMAtPrime
    (p : Nat) (hp : IsPrime p) : Type :=
  Localization.AtPrime (T36EMHeightOne p hp).asIdeal

/-- The same project prime gives a genuine DVR localization. -/
theorem T36EM_atPrime_isDVR
    {p : Nat} (hp : IsPrime p) :
    IsDiscreteValuationRing (T36EMAtPrime p hp) := by
  letI : (T36EMHeightOne p hp).asIdeal.IsPrime :=
    (T36EMHeightOne p hp).isPrime
  exact
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ℤ (T36EMHeightOne p hp).ne_bot (T36EMAtPrime p hp)

/-- Canonical height-one valuation on an embedded natural detects p-divisibility. -/
theorem T36EM_canonical_lt_one_iff_dvd
    {p n : Nat} (hp : IsPrime p) :
    (T36EMHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1
      ↔ p ∣ n := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change (n : ℤ) ∈ T36EMPrimeIdeal p ↔ p ∣ n
  unfold T36EMPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- Canonical height-one valuation on an embedded natural is one iff p does not divide it. -/
theorem T36EM_canonical_eq_one_iff_not_dvd
    {p n : Nat} (hp : IsPrime p) :
    (T36EMHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1
      ↔ ¬ p ∣ n := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  change (n : ℤ) ∉ T36EMPrimeIdeal p ↔ ¬ p ∣ n
  unfold T36EMPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- The AtPrime-DVR valuation has the same <1 divisibility test on embedded naturals. -/
theorem T36EM_local_lt_one_iff_dvd
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hp)] :
    valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal (T36EMAtPrime p hp))
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1
      ↔ p ∣ n := by
  rw [IsScalarTower.algebraMap_apply
    ℤ (T36EMAtPrime p hp) (FractionRing ℤ)]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change
    (algebraMap ℤ (T36EMAtPrime p hp)) (n : ℤ) ∈
        IsLocalRing.maximalIdeal (T36EMAtPrime p hp) ↔ p ∣ n
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
    (T36EMAtPrime p hp) (T36EMHeightOne p hp).asIdeal]
  change (n : ℤ) ∈ T36EMPrimeIdeal p ↔ p ∣ n
  unfold T36EMPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- The AtPrime-DVR valuation has the same =1 nondivisibility test. -/
theorem T36EM_local_eq_one_iff_not_dvd
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hp)] :
    valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal (T36EMAtPrime p hp))
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1
      ↔ ¬ p ∣ n := by
  rw [IsScalarTower.algebraMap_apply
    ℤ (T36EMAtPrime p hp) (FractionRing ℤ)]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  change
    (algebraMap ℤ (T36EMAtPrime p hp)) (n : ℤ) ∉
        IsLocalRing.maximalIdeal (T36EMAtPrime p hp) ↔ ¬ p ∣ n
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
    (T36EMAtPrime p hp) (T36EMHeightOne p hp).asIdeal]
  change (n : ℤ) ∉ T36EMPrimeIdeal p ↔ ¬ p ∣ n
  unfold T36EMPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- E1 compatibility in the exact bad-reduction predicate consumed by Mathlib. -/
theorem T36EM_canonical_local_lt_one_iff
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hp)] :
    ((T36EMHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1)
      ↔
    (valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal (T36EMAtPrime p hp))
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1) := by
  rw [T36EM_canonical_lt_one_iff_dvd hp,
    T36EM_local_lt_one_iff_dvd hp]

/-- E1 compatibility in the exact c4-unit predicate consumed by Mathlib. -/
theorem T36EM_canonical_local_eq_one_iff
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hp)] :
    ((T36EMHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1)
      ↔
    (valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal (T36EMAtPrime p hp))
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1) := by
  rw [T36EM_canonical_eq_one_iff_not_dvd hp,
    T36EM_local_eq_one_iff_not_dvd hp]

/-- Integral Frey model Y² = X(X-A)(X+B), A=a^x, B=b^y. -/
def T36EMFreyCurveZ
    (a b x y : Nat) : WeierstrassCurve ℤ :=
  let A : ℤ := (a ^ x : Nat)
  let B : ℤ := (b ^ y : Nat)
  ⟨0, B - A, 0, -(A * B), 0⟩

/-- The exact same Frey model over Frac(Z). -/
noncomputable def T36EMFreyCurve
    (a b x y : Nat) : WeierstrassCurve (FractionRing ℤ) :=
  (T36EMFreyCurveZ a b x y).baseChange (FractionRing ℤ)

/-- c4 of the integral Frey model is exactly the T32 kernel. -/
theorem T36EM_freyZ_c4
    (a b x y : Nat) :
    (T36EMFreyCurveZ a b x y).c₄ =
      (T32FreyC4Kernel a b x y : ℤ) := by
  unfold T36EMFreyCurveZ T32FreyC4Kernel
    WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
  norm_num <;> push_cast <;> ring

/-- Delta of the integral Frey model is exactly the T24 algebraic kernel. -/
theorem T36EM_freyZ_delta
    (a b x y : Nat) :
    (T36EMFreyCurveZ a b x y).Δ =
      (T24FreyDiscriminantKernel a b x y : ℤ) := by
  unfold T36EMFreyCurveZ T24FreyDiscriminantKernel
    WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈
  norm_num <;> push_cast <;> ring

/-- c4 after base change remains exactly the embedded T32 kernel. -/
theorem T36EM_frey_c4
    (a b x y : Nat) :
    (T36EMFreyCurve a b x y).c₄ =
      algebraMap ℤ (FractionRing ℤ)
        (T32FreyC4Kernel a b x y : ℤ) := by
  unfold T36EMFreyCurve WeierstrassCurve.baseChange
  rw [WeierstrassCurve.map_c₄, T36EM_freyZ_c4]

/-- Delta after base change remains exactly the embedded T24 kernel. -/
theorem T36EM_frey_delta
    (a b x y : Nat) :
    (T36EMFreyCurve a b x y).Δ =
      algebraMap ℤ (FractionRing ℤ)
        (T24FreyDiscriminantKernel a b x y : ℤ) := by
  unfold T36EMFreyCurve WeierstrassCurve.baseChange
  rw [WeierstrassCurve.map_Δ, T36EM_freyZ_delta]

/-- Under the Beal equation, the same Delta is the embedded T24 Beal form. -/
theorem T36EM_frey_delta_beal
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    (T36EMFreyCurve a b x y).Δ =
      algebraMap ℤ (FractionRing ℤ)
        (T24FreyDiscriminantBeal a b c x y z : ℤ) := by
  rw [T36EM_frey_delta]
  apply congrArg (algebraMap ℤ (FractionRing ℤ))
  exact_mod_cast T24_frey_discriminant_rewrite heq

/-- T33 discriminant divisibility becomes the exact local-DVR bad-reduction valuation. -/
theorem T36EM_delta_local
    {a b c x y z p : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hInput : T33OddPrimeReductionInput a b c x y z p)
    [hP : (T36EMHeightOne p hInput.1).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hInput.1)] :
    valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal
          (T36EMAtPrime p hInput.1))
        (T36EMFreyCurve a b x y).Δ < 1 := by
  rw [T36EM_frey_delta_beal heq]
  exact (T36EM_local_lt_one_iff_dvd hInput.1).2
    hInput.2.2.1

/-- T33 c4 nondivisibility becomes the exact local-DVR c4-unit valuation. -/
theorem T36EM_c4_local
    {a b c x y z p : Nat}
    (hInput : T33OddPrimeReductionInput a b c x y z p)
    [hP : (T36EMHeightOne p hInput.1).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hInput.1)] :
    valuation (FractionRing ℤ)
        (IsDiscreteValuationRing.maximalIdeal
          (T36EMAtPrime p hInput.1))
        (T36EMFreyCurve a b x y).c₄ = 1 := by
  rw [T36EM_frey_c4]
  exact (T36EM_local_eq_one_iff_not_dvd hInput.1).2
    hInput.2.2.2.1

/-- Generic E2 lemma: an integral model whose c4 is a DVR-unit is already minimal. -/
theorem T36EM_isMinimal_of_integral_c4_unit
    {R K : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K}
    (hInt : WeierstrassCurve.IsIntegral R W)
    (hc4 :
      valuation K (IsDiscreteValuationRing.maximalIdeal R) W.c₄ = 1) :
    WeierstrassCurve.IsMinimal R W := by
  letI : WeierstrassCurve.IsIntegral R W := hInt
  refine ⟨?_⟩
  refine ⟨by simpa using hInt, ?_⟩
  intro C hC _
  letI : WeierstrassCurve.IsIntegral R (C • W) := hC
  simp only [one_smul]
  rw [← Subtype.coe_le_coe]
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W)]
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]
  have hc4C_le :
      valuation K (IsDiscreteValuationRing.maximalIdeal R) (C • W).c₄ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_c₄_eq R (C • W)]
    exact
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (IsDiscreteValuationRing.maximalIdeal R)
        (WeierstrassCurve.integralModel R (C • W)).c₄
  rw [WeierstrassCurve.variableChange_c₄] at hc4C_le
  simp only [map_mul, map_pow, hc4, mul_one] at hc4C_le
  have huInv_le :
      valuation K (IsDiscreteValuationRing.maximalIdeal R)
          ((C.u⁻¹ : K)) ≤ 1 := by
    simpa only [Units.val_inv_eq_inv_val] using
      (pow_le_one_iff (by decide : (4 : Nat) ≠ 0)).mp hc4C_le
  have huInv12_le :
      (valuation K (IsDiscreteValuationRing.maximalIdeal R)
          ((C.u⁻¹ : K))) ^ 12 ≤ 1 := by
    exact (pow_le_one_iff (by decide : (12 : Nat) ≠ 0)).mpr huInv_le
  rw [WeierstrassCurve.variableChange_Δ]
  simp only [map_mul, map_pow]
  simpa using
    (mul_le_mul_left
      huInv12_le
      (valuation K (IsDiscreteValuationRing.maximalIdeal R) W.Δ))

/-- Frey model over the local DVR. -/
noncomputable def T36EMFreyCurveLocal
    (a b x y p : Nat) (hp : IsPrime p) :
    WeierstrassCurve (T36EMAtPrime p hp) :=
  (T36EMFreyCurveZ a b x y).baseChange (T36EMAtPrime p hp)

/-- Local Frey model base-changes to the exact fraction-field Frey model. -/
theorem T36EM_local_baseChange_eq
    {a b x y p : Nat} {hp : IsPrime p}
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime] :
    (T36EMFreyCurveLocal a b x y p hp).baseChange (FractionRing ℤ) =
      T36EMFreyCurve a b x y := by
  ext <;>
    simp only [T36EMFreyCurveLocal, T36EMFreyCurve,
      WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] <;>
    exact
      (IsScalarTower.algebraMap_apply
        ℤ (T36EMAtPrime p hp) (FractionRing ℤ) _).symm

/-- The exact fraction-field Frey equation is integral over Z_(p). -/
theorem T36EM_frey_isIntegral
    {a b x y p : Nat} {hp : IsPrime p}
    [hP : (T36EMHeightOne p hp).asIdeal.IsPrime] :
    WeierstrassCurve.IsIntegral
      (T36EMAtPrime p hp)
      (T36EMFreyCurve a b x y) := by
  refine ⟨?_⟩
  exact ⟨T36EMFreyCurveLocal a b x y p hp,
    (T36EM_local_baseChange_eq
      (a := a) (b := b) (x := x) (y := y)
      (p := p) (hp := hp)).symm⟩

/-- E2: T33 c4-unit input forces the same Frey model to be minimal. -/
theorem T36EM_frey_isMinimal
    {a b c x y z p : Nat}
    (hInput : T33OddPrimeReductionInput a b c x y z p)
    [hP : (T36EMHeightOne p hInput.1).asIdeal.IsPrime]
    [hDVR : IsDiscreteValuationRing (T36EMAtPrime p hInput.1)] :
    WeierstrassCurve.IsMinimal
      (T36EMAtPrime p hInput.1)
      (T36EMFreyCurve a b x y) := by
  exact T36EM_isMinimal_of_integral_c4_unit
    (T36EM_frey_isIntegral
      (a := a) (b := b) (x := x) (y := y)
      (p := p) (hp := hInput.1))
    (T36EM_c4_local hInput)

/-- E1 + E2 close Mathlib's genuine multiplicative-reduction predicate. -/
theorem T36EM_hasMultiplicativeReduction
    {a b c x y z p : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hInput : T33OddPrimeReductionInput a b c x y z p) :
    letI : (T36EMHeightOne p hInput.1).asIdeal.IsPrime :=
      (T36EMHeightOne p hInput.1).isPrime
    letI : IsDiscreteValuationRing (T36EMAtPrime p hInput.1) :=
      T36EM_atPrime_isDVR hInput.1
    (T36EMFreyCurve a b x y).HasMultiplicativeReduction
      (T36EMAtPrime p hInput.1) := by
  letI : (T36EMHeightOne p hInput.1).asIdeal.IsPrime :=
    (T36EMHeightOne p hInput.1).isPrime
  letI : IsDiscreteValuationRing (T36EMAtPrime p hInput.1) :=
    T36EM_atPrime_isDVR hInput.1
  letI : WeierstrassCurve.IsMinimal
      (T36EMAtPrime p hInput.1)
      (T36EMFreyCurve a b x y) :=
    T36EM_frey_isMinimal hInput
  exact {
    badReduction := T36EM_delta_local heq hInput
    multiplicativeReduction := T36EM_c4_local hInput
  }

#print axioms MCore.T36EM_canonical_lt_one_iff_dvd
#print axioms MCore.T36EM_local_lt_one_iff_dvd
#print axioms MCore.T36EM_canonical_local_lt_one_iff
#print axioms MCore.T36EM_freyZ_c4
#print axioms MCore.T36EM_freyZ_delta
#print axioms MCore.T36EM_delta_local
#print axioms MCore.T36EM_c4_local
#print axioms MCore.T36EM_isMinimal_of_integral_c4_unit
#print axioms MCore.T36EM_frey_isMinimal
#print axioms MCore.T36EM_hasMultiplicativeReduction

end MCore
