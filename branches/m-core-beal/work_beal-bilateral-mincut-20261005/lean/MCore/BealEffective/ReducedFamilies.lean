import MCore.BealEffective.PrimitiveConsequences

namespace MCore
namespace BealEffective

/-- Reduced exponent normal form: either 4 or an odd prime. -/
def ReducedExponent (r : Nat) : Prop :=
  2 < r ∧ (r = 4 ∨ IsPrime r)

def ExponentReduces (n : Nat) : Prop :=
  ∃ r k : Nat, n = r * k ∧ ReducedExponent r

private theorem two_factor_gt_one
    {n k : Nat}
    (hk : n = 2 * k)
    (hn : 2 < n) :
    1 < k := by
  omega

/-- Constructive exponent reduction using the frozen K10 prime-divisor producer. -/
theorem exponent_reduction
    {n : Nat}
    (hn : 2 < n) :
    ExponentReduces n := by
  have hn1 : 1 < n := Nat.lt_trans (by decide : 1 < 2) hn
  rcases primeDivisorProperty_proved n hn1 with ⟨p, hp, hpn⟩
  by_cases hp2 : p = 2
  · subst p
    rcases hpn with ⟨k, hk⟩
    have hk1 : 1 < k := two_factor_gt_one hk hn
    rcases primeDivisorProperty_proved k hk1 with ⟨q, hq, hqk⟩
    by_cases hq2 : q = 2
    · subst q
      rcases hqk with ⟨m, hkm⟩
      refine ⟨4, m, ?_, ?_⟩
      · calc
          n = 2 * k := hk
          _ = 2 * (2 * m) := congrArg (fun t : Nat => 2 * t) hkm
          _ = 4 * m := by omega
      · exact ⟨by decide, Or.inl rfl⟩
    · have h2le : 2 ≤ q := Nat.succ_le_of_lt hq.1
      have h2lt : 2 < q := Nat.lt_of_le_of_ne h2le (Ne.symm hq2)
      have hkn : k ∣ n := by
        refine ⟨2, ?_⟩
        omega
      have hqn : q ∣ n := nat_dvd_trans hqk hkn
      rcases hqn with ⟨m, hnm⟩
      exact ⟨q, m, hnm, h2lt, Or.inr hq⟩
  · have h2le : 2 ≤ p := Nat.succ_le_of_lt hp.1
    have h2lt : 2 < p := Nat.lt_of_le_of_ne h2le (Ne.symm hp2)
    rcases hpn with ⟨k, hnk⟩
    exact ⟨p, k, hnk, h2lt, Or.inr hp⟩

theorem pow_mul_outer (a k r : Nat) :
    (a ^ k) ^ r = a ^ (k * r) := by
  exact (Nat.pow_mul a k r).symm

/-- Reduced primitive candidate generated from a hypothetical gcd3=1 datum. -/
structure ReducedPrimitiveCandidate where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_reduced : ReducedExponent x
  y_reduced : ReducedExponent y
  z_reduced : ReducedExponent z
  equation : a ^ x + b ^ y = c ^ z
  no_common : ¬ ∃ q : Nat, CommonDivisor q a b c

theorem powered_no_common
    {a b c ka kb kc : Nat}
    (hNoCommon : ¬ ∃ q : Nat, CommonDivisor q a b c) :
    ¬ ∃ q : Nat, CommonDivisor q (a ^ ka) (b ^ kb) (c ^ kc) := by
  intro h
  rcases h with ⟨q, hqgt, hqa, hqb, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpaPow : p ∣ a ^ ka := nat_dvd_trans hpq hqa
  have hpbPow : p ∣ b ^ kb := nat_dvd_trans hpq hqb
  have hpcPow : p ∣ c ^ kc := nat_dvd_trans hpq hqc
  have hpa : p ∣ a := prime_dvd_pow_reflect hp hpaPow
  have hpb : p ∣ b := prime_dvd_pow_reflect hp hpbPow
  have hpc : p ∣ c := prime_dvd_pow_reflect hp hpcPow
  exact hNoCommon ⟨p, hp.1, hpa, hpb, hpc⟩

/-- Any failure of the terminal lower bound produces a reduced primitive equation. -/
theorem failed_lowerBound_to_reduced
    (d : BealData)
    (hFail : ¬ 1 < gcd3 d) :
    Nonempty ReducedPrimitiveCandidate := by
  have hg : gcd3 d = 1 := gcd3_eq_one_of_not_lowerBound d hFail
  have hNoCommon : ¬ ∃ q : Nat, CommonDivisor q d.a d.b d.c := by
    intro h
    have hlt := (commonDivisor_iff_one_lt_nestedGCD d).mp h
    have : 1 < gcd3 d := by simpa [gcd3] using hlt
    exact hFail this
  rcases exponent_reduction d.x_gt_two with ⟨rx, kx, hx, hrx⟩
  rcases exponent_reduction d.y_gt_two with ⟨ry, ky, hy, hry⟩
  rcases exponent_reduction d.z_gt_two with ⟨rz, kz, hz, hrz⟩
  have hax : (d.a ^ kx) ^ rx = d.a ^ d.x := by
    calc
      (d.a ^ kx) ^ rx = d.a ^ (kx * rx) := pow_mul_outer d.a kx rx
      _ = d.a ^ (rx * kx) := by rw [Nat.mul_comm]
      _ = d.a ^ d.x := by rw [← hx]
  have hby : (d.b ^ ky) ^ ry = d.b ^ d.y := by
    calc
      (d.b ^ ky) ^ ry = d.b ^ (ky * ry) := pow_mul_outer d.b ky ry
      _ = d.b ^ (ry * ky) := by rw [Nat.mul_comm]
      _ = d.b ^ d.y := by rw [← hy]
  have hcz : (d.c ^ kz) ^ rz = d.c ^ d.z := by
    calc
      (d.c ^ kz) ^ rz = d.c ^ (kz * rz) := pow_mul_outer d.c kz rz
      _ = d.c ^ (rz * kz) := by rw [Nat.mul_comm]
      _ = d.c ^ d.z := by rw [← hz]
  refine ⟨{
    a := d.a ^ kx
    b := d.b ^ ky
    c := d.c ^ kz
    x := rx
    y := ry
    z := rz
    a_pos := Nat.pow_pos d.a_pos
    b_pos := Nat.pow_pos d.b_pos
    c_pos := Nat.pow_pos d.c_pos
    x_reduced := hrx
    y_reduced := hry
    z_reduced := hrz
    equation := ?_
    no_common := powered_no_common hNoCommon
  }⟩
  calc
    (d.a ^ kx) ^ rx + (d.b ^ ky) ^ ry
        = d.a ^ d.x + d.b ^ d.y := by rw [hax, hby]
    _ = d.c ^ d.z := d.equation
    _ = (d.c ^ kz) ^ rz := hcz.symm

def OddPrimeExponent (p : Nat) : Prop :=
  IsPrime p ∧ 2 < p

def AllFour (x y z : Nat) : Prop :=
  x = 4 ∧ y = 4 ∧ z = 4

def EqualOddPrime (x y z : Nat) : Prop :=
  ∃ p : Nat, OddPrimeExponent p ∧ x = p ∧ y = p ∧ z = p

def TwoFourPrime (x y z : Nat) : Prop :=
  (x = 4 ∧ y = 4 ∧ OddPrimeExponent z) ∨
  (x = 4 ∧ z = 4 ∧ OddPrimeExponent y) ∨
  (y = 4 ∧ z = 4 ∧ OddPrimeExponent x)

def OneFourEqualPrimes (x y z : Nat) : Prop :=
  (x = 4 ∧ OddPrimeExponent y ∧ z = y) ∨
  (y = 4 ∧ OddPrimeExponent x ∧ z = x) ∨
  (z = 4 ∧ OddPrimeExponent x ∧ y = x)

def OneFourDistinctPrimes (x y z : Nat) : Prop :=
  (x = 4 ∧ OddPrimeExponent y ∧ OddPrimeExponent z ∧ y ≠ z) ∨
  (y = 4 ∧ OddPrimeExponent x ∧ OddPrimeExponent z ∧ x ≠ z) ∨
  (z = 4 ∧ OddPrimeExponent x ∧ OddPrimeExponent y ∧ x ≠ y)

def TwoEqualOddPrimes (x y z : Nat) : Prop :=
  (OddPrimeExponent x ∧ y = x ∧ OddPrimeExponent z ∧ x ≠ z) ∨
  (OddPrimeExponent x ∧ z = x ∧ OddPrimeExponent y ∧ x ≠ y) ∨
  (OddPrimeExponent y ∧ z = y ∧ OddPrimeExponent x ∧ y ≠ x)

def ThreeDistinctOddPrimes (x y z : Nat) : Prop :=
  OddPrimeExponent x ∧ OddPrimeExponent y ∧ OddPrimeExponent z ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z

def SevenFamilySplit (x y z : Nat) : Prop :=
  AllFour x y z ∨
  EqualOddPrime x y z ∨
  TwoFourPrime x y z ∨
  OneFourEqualPrimes x y z ∨
  OneFourDistinctPrimes x y z ∨
  TwoEqualOddPrimes x y z ∨
  ThreeDistinctOddPrimes x y z

private theorem oddPrime_of_reduced_ne_four
    {r : Nat}
    (hr : ReducedExponent r)
    (hne : r ≠ 4) :
    OddPrimeExponent r := by
  exact ⟨hr.2.resolve_left hne, hr.1⟩

/-- Exhaustive classification of any reduced exponent triple into two classical
branches plus five residual mixed families. -/
theorem reduced_signature_seven_family
    {x y z : Nat}
    (hx : ReducedExponent x)
    (hy : ReducedExponent y)
    (hz : ReducedExponent z) :
    SevenFamilySplit x y z := by
  by_cases hx4 : x = 4
  · by_cases hy4 : y = 4
    · by_cases hz4 : z = 4
      · exact Or.inl ⟨hx4, hy4, hz4⟩
      ·
        have hC : TwoFourPrime x y z :=
          Or.inl ⟨hx4, hy4, oddPrime_of_reduced_ne_four hz hz4⟩
        exact Or.inr (Or.inr (Or.inl hC))
    · by_cases hz4 : z = 4
      ·
        have hC : TwoFourPrime x y z :=
          Or.inr (Or.inl ⟨hx4, hz4, oddPrime_of_reduced_ne_four hy hy4⟩)
        exact Or.inr (Or.inr (Or.inl hC))
      ·
        have hyp := oddPrime_of_reduced_ne_four hy hy4
        have hzp := oddPrime_of_reduced_ne_four hz hz4
        by_cases hyz : y = z
        ·
          have hD : OneFourEqualPrimes x y z :=
            Or.inl ⟨hx4, hyp, hyz.symm⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
        ·
          have hE : OneFourDistinctPrimes x y z :=
            Or.inl ⟨hx4, hyp, hzp, hyz⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE))))
  · by_cases hy4 : y = 4
    · by_cases hz4 : z = 4
      ·
        have hC : TwoFourPrime x y z :=
          Or.inr (Or.inr ⟨hy4, hz4, oddPrime_of_reduced_ne_four hx hx4⟩)
        exact Or.inr (Or.inr (Or.inl hC))
      ·
        have hxp := oddPrime_of_reduced_ne_four hx hx4
        have hzp := oddPrime_of_reduced_ne_four hz hz4
        by_cases hxz : x = z
        ·
          have hD : OneFourEqualPrimes x y z :=
            Or.inr (Or.inl ⟨hy4, hxp, hxz.symm⟩)
          exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
        ·
          have hE : OneFourDistinctPrimes x y z :=
            Or.inr (Or.inl ⟨hy4, hxp, hzp, hxz⟩)
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE))))
    · by_cases hz4 : z = 4
      ·
        have hxp := oddPrime_of_reduced_ne_four hx hx4
        have hyp := oddPrime_of_reduced_ne_four hy hy4
        by_cases hxy : x = y
        ·
          have hD : OneFourEqualPrimes x y z :=
            Or.inr (Or.inr ⟨hz4, hxp, hxy.symm⟩)
          exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
        ·
          have hE : OneFourDistinctPrimes x y z :=
            Or.inr (Or.inr ⟨hz4, hxp, hyp, hxy⟩)
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE))))
      ·
        have hxp := oddPrime_of_reduced_ne_four hx hx4
        have hyp := oddPrime_of_reduced_ne_four hy hy4
        have hzp := oddPrime_of_reduced_ne_four hz hz4
        by_cases hxy : x = y
        · by_cases hyz : y = z
          ·
            have hxz : x = z := hxy.trans hyz
            have hB : EqualOddPrime x y z :=
              ⟨x, hxp, rfl, hxy.symm, hxz.symm⟩
            exact Or.inr (Or.inl hB)
          ·
            have hxz : x ≠ z := by
              intro hxz
              apply hyz
              exact hxy.symm.trans hxz
            have hF : TwoEqualOddPrimes x y z :=
              Or.inl ⟨hxp, hxy.symm, hzp, hxz⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hF)))))
        · by_cases hxz : x = z
          ·
            have hF : TwoEqualOddPrimes x y z :=
              Or.inr (Or.inl ⟨hxp, hxz.symm, hyp, hxy⟩)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hF)))))
          · by_cases hyz : y = z
            ·
              have hyx : y ≠ x := by
                intro hyx
                exact hxy hyx.symm
              have hF : TwoEqualOddPrimes x y z :=
                Or.inr (Or.inr ⟨hyp, hyz.symm, hxp, hyx⟩)
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hF)))))
            ·
              have hG : ThreeDistinctOddPrimes x y z :=
                ⟨hxp, hyp, hzp, hxy, hxz, hyz⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hG)))))

theorem failed_lowerBound_seven_family
    (d : BealData)
    (hFail : ¬ 1 < gcd3 d) :
    ∃ r : ReducedPrimitiveCandidate,
      SevenFamilySplit r.x r.y r.z := by
  rcases failed_lowerBound_to_reduced d hFail with ⟨r⟩
  exact ⟨r, reduced_signature_seven_family
    r.x_reduced r.y_reduced r.z_reduced⟩

#print axioms MCore.BealEffective.exponent_reduction
#print axioms MCore.BealEffective.failed_lowerBound_to_reduced
#print axioms MCore.BealEffective.reduced_signature_seven_family
#print axioms MCore.BealEffective.failed_lowerBound_seven_family

end BealEffective
end MCore
