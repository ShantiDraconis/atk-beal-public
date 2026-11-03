import MCore.T62

namespace MCore

/-!
T63 — ACTUAL ODD-PRIME MULTIPLICATIVE REDUCTION

This module converts the arithmetic packet frozen at T60 into Mathlib's
semantic HasMultiplicativeReduction for the actual T61 generalized Frey
curve, at every odd natural prime dividing the raw discriminant.

No conductor exponent or level-lowering statement is asserted here.
-/

open IsDedekindDomain
open NumberField
open WeierstrassCurve
open IsDiscreteValuationRing
open IsLocalRing

theorem T63_natCast_mem_primePlace_iff
    {p n : Nat}
    (hp : Nat.Prime p) :
    ((n : 𝓞 ℚ) ∈ (T62PrimePlace p hp).asIdeal) ↔ p ∣ n := by
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  let v := T62PrimePlace p hp
  have hgen : Rat.HeightOneSpectrum.natGenerator v = p :=
    T62_primePlace_natGenerator p hp
  have hmap :
      e (n : 𝓞 ℚ) ∈ v.asIdeal.map e ↔ ((n : 𝓞 ℚ) ∈ v.asIdeal) :=
    Ideal.apply_mem_of_equiv_iff
  have hdiv := Rat.HeightOneSpectrum.natGenerator_dvd_iff v (n := n)
  rw [hgen] at hdiv
  have he : e (n : 𝓞 ℚ) = (n : ℤ) := by
    simp [e]
  rw [he] at hmap
  exact hmap.symm.trans hdiv.symm

theorem T63_isUnit_natCast_localRing
    {p n : Nat}
    (hp : Nat.Prime p)
    (hndvd : ¬ p ∣ n) :
    IsUnit ((n : T62LocalRing p hp)) := by
  let v := T62PrimePlace p hp
  let R := T62LocalRing p hp
  have hcompl : ((n : 𝓞 ℚ)) ∈ v.asIdeal.primeCompl := by
    intro hmem
    exact hndvd ((T63_natCast_mem_primePlace_iff hp).mp hmem)
  have h :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      R v.asIdeal ((n : 𝓞 ℚ))).mpr hcompl
  simpa [R] using h

theorem T63_freyCurveQ_c4_eq_natKernel
    (a b x y : Nat) :
    (T61FreyCurveQ a b x y).c₄ =
      (T32FreyC4Kernel a b x y : ℚ) := by
  rw [T61_freyCurveQ_c4, T61_c4_matches_T32_kernel]
  norm_num

theorem T63_freyCurveQ_delta_eq_natKernel
    (d : T59ResidualCandidate) :
    (T61FreyCurveQ d.a d.b d.x d.y).Δ =
      (T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z : ℚ) := by
  rw [T61_freyCurveQ_delta, T61_delta_matches_T24_kernel]
  norm_num

theorem T63_freyCurve_hasMultiplicativeReduction_at_odd_bad_prime
    (d : T59ResidualCandidate)
    {q : Nat}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (hDelta :
      q ∣ T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z) :
    (T61FreyCurveQ d.a d.b d.x d.y).HasMultiplicativeReduction
      (T62LocalRing q hq) := by
  let R := T62LocalRing q hq
  let E := T61FreyCurveQ d.a d.b d.x d.y

  have hCorePrime : MCore.IsPrime q :=
    T62_natPrime_to_corePrime hq
  have hPacket : T60OddLocalArithmeticPacket d q :=
    T60_candidate_odd_prime_has_arithmetic_packet
      d hCorePrime hq2 hDelta
  have hc4ndvd : ¬ q ∣ T32FreyC4Kernel d.a d.b d.x d.y :=
    T60_odd_bad_prime_not_dvd_c4 d hPacket

  haveI hInt : WeierstrassCurve.IsIntegral R E := by
    dsimp [R, E]
    exact T62_freyCurveQ_isIntegral d.a d.b d.x d.y q hq

  have huc4 :
      IsUnit ((T32FreyC4Kernel d.a d.b d.x d.y : Nat) : R) :=
    T63_isUnit_natCast_localRing hq hc4ndvd

  have hc4eq :
      E.c₄ = algebraMap R ℚ
        ((T32FreyC4Kernel d.a d.b d.x d.y : Nat) : R) := by
    rw [T63_freyCurveQ_c4_eq_natKernel]
    simp

  have hvalc4 :
      IsDedekindDomain.HeightOneSpectrum.valuation ℚ
        (IsDiscreteValuationRing.maximalIdeal R) E.c₄ = 1 := by
    have hmem :
        E.c₄ ∈ MonoidHom.mker
          ((IsDiscreteValuationRing.maximalIdeal R).valuation ℚ) := by
      rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid]
      exact Submonoid.mem_map.mpr
        ⟨((T32FreyC4Kernel d.a d.b d.x d.y : Nat) : R), huc4, hc4eq.symm⟩
    exact MonoidHom.mem_mker.mp hmem

  have hRawMemO :
      ((T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z : Nat) : 𝓞 ℚ) ∈
        (T62PrimePlace q hq).asIdeal :=
    (T63_natCast_mem_primePlace_iff hq).mpr hDelta

  have hRawMemR :
      ((T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z : Nat) : R) ∈
        IsLocalRing.maximalIdeal R := by
    have hm :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        R (T62PrimePlace q hq).asIdeal
        ((T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z : Nat) : 𝓞 ℚ)).mpr
        hRawMemO
    simpa [R] using hm

  have hDeltaEq :
      E.Δ = algebraMap R ℚ
        ((T24FreyDiscriminantBeal d.a d.b d.c d.x d.y d.z : Nat) : R) := by
    rw [T63_freyCurveQ_delta_eq_natKernel]
    simp

  have hvalDelta :
      IsDedekindDomain.HeightOneSpectrum.valuation ℚ
        (IsDiscreteValuationRing.maximalIdeal R) E.Δ < 1 := by
    rw [hDeltaEq]
    exact
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal R) _).mpr hRawMemR

  exact {
    toIsMinimal := T62_isMinimal_of_valuation_c4_eq_one E hvalc4
    badReduction := hvalDelta
    multiplicativeReduction := hvalc4
  }

#print axioms MCore.T63_natCast_mem_primePlace_iff
#print axioms MCore.T63_isUnit_natCast_localRing
#print axioms MCore.T63_freyCurveQ_c4_eq_natKernel
#print axioms MCore.T63_freyCurveQ_delta_eq_natKernel
#print axioms MCore.T63_freyCurve_hasMultiplicativeReduction_at_odd_bad_prime

end MCore
