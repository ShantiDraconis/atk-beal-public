import MCore.T36C
import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace MCore

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- The height-one prime of Z corresponding to the exact project-prime p. -/
noncomputable def T36DHeightOne
    (p : Nat) (hp : IsPrime p) :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := T36CPrimeIdeal p
  isPrime := T36C_primeIdeal_isPrime hp
  ne_bot := T36C_primeIdeal_ne_bot hp

/-- Exact translation between project divisibility and the canonical p-adic
    valuation on the fraction field of Z. -/
theorem T36D_dvd_iff_valuation_lt_one
    {p n : Nat} (hp : IsPrime p) :
    (T36DHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) < 1
      ↔ p ∣ n := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change (n : ℤ) ∈ T36CPrimeIdeal p ↔ p ∣ n
  unfold T36CPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- Exact complementary translation: nondivisibility is valuation one. -/
theorem T36D_not_dvd_iff_valuation_eq_one
    {p n : Nat} (hp : IsPrime p) :
    (T36DHeightOne p hp).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ) (n : ℤ)) = 1
      ↔ ¬ p ∣ n := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  change (n : ℤ) ∉ T36CPrimeIdeal p ↔ ¬ p ∣ n
  unfold T36CPrimeIdeal
  rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- T33/T36 arithmetic data gives the bad-discriminant valuation statement
    for the exact discriminant kernel. -/
theorem T36D_package_delta_valuation
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p) :
    (T36DHeightOne p hPkg.input.1).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ)
          (T24FreyDiscriminantBeal a b c x y z : ℤ)) < 1 := by
  exact
    (T36D_dvd_iff_valuation_lt_one hPkg.input.1).2
      hPkg.input.2.2.1

/-- T33/T36 arithmetic data gives the c4-unit valuation statement for the
    exact c4 kernel. -/
theorem T36D_package_c4_valuation
    {a b c x y z p : Nat}
    (hPkg : T36OddLocalArithmeticPackage a b c x y z p) :
    (T36DHeightOne p hPkg.input.1).valuation (FractionRing ℤ)
        (algebraMap ℤ (FractionRing ℤ)
          (T32FreyC4Kernel a b x y : ℤ)) = 1 := by
  exact
    (T36D_not_dvd_iff_valuation_eq_one hPkg.input.1).2
      hPkg.input.2.2.2.1

/-- After T36D the elementary divisibility-to-canonical-valuation step is
    closed.  Compatibility with the valuation selected by the local DVR
    reduction API remains explicit rather than being silently identified. -/
structure T36DRemainingBridges where
  canonicalToLocalDVRValuation : T36GapState
  minimality : T36GapState
  conductorExponentOne : T36GapState

def T36DCurrentRemainingBridges : T36DRemainingBridges where
  canonicalToLocalDVRValuation := .openBridge
  minimality := .openBridge
  conductorExponentOne := .openBridge

#print axioms MCore.T36D_dvd_iff_valuation_lt_one
#print axioms MCore.T36D_not_dvd_iff_valuation_eq_one
#print axioms MCore.T36D_package_delta_valuation
#print axioms MCore.T36D_package_c4_valuation

end MCore
