import MCore.T36D
import Mathlib.Tactic

namespace MCore

open WeierstrassCurve
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- Exact c4 identity for the integral Frey model over Z. -/
theorem T36E1_freyZ_c4_eq_nat_kernel (a b x y : Nat) :
    (T36CFreyCurveZ a b x y).c₄ =
      (T32FreyC4Kernel a b x y : ℤ) := by
  unfold T36CFreyCurveZ T32FreyC4Kernel
    WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
  push_cast
  ring

/-- Under the Beal equation, the discriminant of the integral Frey model is
    exactly the T24 natural-number discriminant kernel cast to Z. -/
theorem T36E1_freyZ_delta_eq_nat_beal
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    (T36CFreyCurveZ a b x y).Δ =
      (T24FreyDiscriminantBeal a b c x y z : ℤ) := by
  unfold T36CFreyCurveZ T24FreyDiscriminantBeal
    WeierstrassCurve.Δ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈
  have hz :
      ((a ^ x : Nat) : ℤ) + ((b ^ y : Nat) : ℤ) =
        ((c ^ z : Nat) : ℤ) := by
    exact_mod_cast heq
  rw [hz]
  push_cast
  ring

/-- c4 after base change to the canonical fraction field of Z. -/
theorem T36E1_freyFrac_c4_eq_nat_kernel (a b x y : Nat) :
    (T36CFreyCurveFrac a b x y).c₄ =
      algebraMap ℤ (FractionRing ℤ)
        (T32FreyC4Kernel a b x y : ℤ) := by
  simp [T36CFreyCurveFrac, T36E1_freyZ_c4_eq_nat_kernel]

/-- Delta after base change to the canonical fraction field of Z. -/
theorem T36E1_freyFrac_delta_eq_nat_beal
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    (T36CFreyCurveFrac a b x y).Δ =
      algebraMap ℤ (FractionRing ℤ)
        (T24FreyDiscriminantBeal a b c x y z : ℤ) := by
  simp [T36CFreyCurveFrac, T36E1_freyZ_delta_eq_nat_beal heq]

/-- The valuation used by the local DVR reduction API detects exactly
    divisibility by the original rational prime p on embedded integers.
    This avoids asserting a global equality between two valuation functions. -/
theorem T36E1_localDVR_dvd_iff_valuation_lt_one
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    (IsDiscreteValuationRing.maximalIdeal (T36CLocalRing p)).valuation
        (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1
      ↔ p ∣ n := by
  rw [← IsScalarTower.algebraMap_apply ℤ (T36CLocalRing p) (FractionRing ℤ)]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
    (T36CLocalRing p) (T36CPrimeIdeal p)]
  unfold T36CPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- Complementary unit criterion for the exact same local-DVR valuation. -/
theorem T36E1_localDVR_not_dvd_iff_valuation_eq_one
    {p n : Nat} (hp : IsPrime p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    (IsDiscreteValuationRing.maximalIdeal (T36CLocalRing p)).valuation
        (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1
      ↔ ¬ p ∣ n := by
  rw [← IsScalarTower.algebraMap_apply ℤ (T36CLocalRing p) (FractionRing ℤ)]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
    (T36CLocalRing p) (T36CPrimeIdeal p)]
  unfold T36CPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- T36 arithmetic data gives bad discriminant in the exact valuation consumed
    by Mathlib's local reduction classes. -/
theorem T36E1_package_delta_localDVR
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    (IsDiscreteValuationRing.maximalIdeal (T36CLocalRing p)).valuation
        (FractionRing ℤ)
        (T36CFreyCurveFrac a b x y).Δ < 1 := by
  rw [T36E1_freyFrac_delta_eq_nat_beal hPkg.equation]
  exact
    (T36E1_localDVR_dvd_iff_valuation_lt_one hPkg.input.1).2
      hPkg.input.2.2.1

/-- T36 arithmetic data gives c4 a unit in that same local-DVR valuation. -/
theorem T36E1_package_c4_localDVR
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p)
    [hP : (T36CPrimeIdeal p).IsPrime]
    [hDVR : IsDiscreteValuationRing (T36CLocalRing p)] :
    (IsDiscreteValuationRing.maximalIdeal (T36CLocalRing p)).valuation
        (FractionRing ℤ)
        (T36CFreyCurveFrac a b x y).c₄ = 1 := by
  rw [T36E1_freyFrac_c4_eq_nat_kernel]
  exact
    (T36E1_localDVR_not_dvd_iff_valuation_eq_one hPkg.input.1).2
      hPkg.input.2.2.2.1

/-- E1 status after this module: valuation compatibility is no longer a
    scientific assumption if all theorems above compile. Minimality and
    conductor exponent one remain separate gates. -/
structure T36E1RemainingBridges where
  minimality : T36GapState
  conductorExponentOne : T36GapState

def T36E1CurrentRemainingBridges : T36E1RemainingBridges where
  minimality := .openBridge
  conductorExponentOne := .openBridge

#print axioms MCore.T36E1_freyZ_c4_eq_nat_kernel
#print axioms MCore.T36E1_freyZ_delta_eq_nat_beal
#print axioms MCore.T36E1_localDVR_dvd_iff_valuation_lt_one
#print axioms MCore.T36E1_localDVR_not_dvd_iff_valuation_eq_one
#print axioms MCore.T36E1_package_delta_localDVR
#print axioms MCore.T36E1_package_c4_localDVR

end MCore
