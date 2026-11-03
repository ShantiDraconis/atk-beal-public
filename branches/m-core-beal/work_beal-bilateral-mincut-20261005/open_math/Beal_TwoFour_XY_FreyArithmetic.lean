import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- Raw Frey discriminant kernel for Y^2 = X(X-a^x)(X+b^y). -/
def XYFreyDiscriminantKernel
    (a b x y : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (a ^ x + b ^ y) ^ 2

/-- Beal-normal form of the same raw discriminant. -/
def XYFreyDiscriminantBeal
    (a b c x y z : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (c ^ z) ^ 2

theorem xy_frey_discriminant_rewrite
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    XYFreyDiscriminantKernel a b x y =
      XYFreyDiscriminantBeal a b c x y z := by
  unfold XYFreyDiscriminantKernel XYFreyDiscriminantBeal
  rw [heq]

private def xyFreyData (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

private theorem xyFreyPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (xyFreyData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (xyFreyData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (xyFreyData r) h)

private theorem xyFreyExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (xyFreyData r) (xyFreyPairwise r)

private theorem xyFrey_gcd_ab
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.b = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hda hdb
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hda with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.a_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((xyFreyPairwise r).1 ⟨d, hdgt, hda, hdb⟩)

private theorem xyFrey_gcd_ac
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.c = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hda hdc
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hda with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.a_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((xyFreyPairwise r).2.1 ⟨d, hdgt, hda, hdc⟩)

private theorem xyFrey_gcd_bc
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.b r.c = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdb hdc
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hdb with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.b_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((xyFreyPairwise r).2.2 ⟨d, hdgt, hdb, hdc⟩)

/--
Exact arithmetic packet supplied to the modular/Frey route for orbit A.
No conductor, modularity, irreducibility, or level-lowering conclusion is
stored here.
-/
structure XYFourPrimeFreyArithmeticPacket
    (r : ReducedPrimitiveCandidate) : Prop where
  hx : r.x = 4
  hy : r.y = 4
  hzPrime : OddPrimeExponent r.z
  equation : r.a ^ 4 + r.b ^ 4 = r.c ^ r.z
  pairwise :
    Nat.gcd r.a r.b = 1 ∧
    Nat.gcd r.a r.c = 1 ∧
    Nat.gcd r.b r.c = 1
  exactlyOneEven : ExactlyOneEven r.a r.b r.c
  rhsNotEven : ¬ Even r.c
  discriminant :
    XYFreyDiscriminantKernel r.a r.b r.x r.y =
      XYFreyDiscriminantBeal r.a r.b r.c r.x r.y r.z

private theorem xyFrey_even_pow8
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  rw [hk, hm]
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem xyFrey_pow_mod_congr
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem xyFrey_odd_fourth8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  have hres :
      n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hpar : (n % 8) % 2 = 1 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    omega
  rcases hres with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply xyFrey_pow_mod_congr
      simp
    rw [hc, h]

private theorem xyFrey_notEven_mod2_one
    (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hm hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem xyFrey_rhs_not_even
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    ¬ Even r.c := by
  intro hc
  have hE := xyFreyExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (xyFrey_notEven_mod2_one r.a).mp hB.1
    · exact (xyFrey_notEven_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (xyFrey_notEven_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (xyFrey_notEven_mod2_one r.b).mp hC.2.1
  have hA8 : r.a ^ 4 % 8 = 1 := xyFrey_odd_fourth8 haOdd
  have hB8 : r.b ^ 4 % 8 = 1 := xyFrey_odd_fourth8 hbOdd
  have hC8 : r.c ^ r.z % 8 = 0 :=
    xyFrey_even_pow8 hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  have hbad : (1 + 1) % 8 = 0 := by
    simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
  simp at hbad

def xyFourPrimeFreyArithmeticPacket
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    XYFourPrimeFreyArithmeticPacket r where
  hx := hx
  hy := hy
  hzPrime := hzPrime
  equation := by simpa [hx, hy] using r.equation
  pairwise := ⟨xyFrey_gcd_ab r, xyFrey_gcd_ac r, xyFrey_gcd_bc r⟩
  exactlyOneEven := xyFreyExactlyOneEven r
  rhsNotEven := xyFrey_rhs_not_even r hx hy
  discriminant := xy_frey_discriminant_rewrite r.equation

/--
On the xy-four orbit the raw discriminant has the exact exponent pattern
16 * a^8 * b^8 * c^(2z).
-/
theorem xy_four_frey_discriminant_normal_form
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4) :
    XYFreyDiscriminantBeal r.a r.b r.c r.x r.y r.z =
      16 * r.a ^ 8 * r.b ^ 8 * r.c ^ (2 * r.z) := by
  have ha8 : (r.a ^ 4) ^ 2 = r.a ^ 8 := by
    rw [← Nat.pow_mul]
  have hb8 : (r.b ^ 4) ^ 2 = r.b ^ 8 := by
    rw [← Nat.pow_mul]
  have hcz : (r.c ^ r.z) ^ 2 = r.c ^ (2 * r.z) := by
    rw [← Nat.pow_mul]
    simp [Nat.mul_comm]
  unfold XYFreyDiscriminantBeal
  rw [hx, hy, ha8, hb8, hcz]

private theorem xyFrey_not_dvd_other_of_gcd_one
    {q u v : Nat}
    (hq : IsPrime q)
    (hu : q ∣ u)
    (hG : Nat.gcd u v = 1) :
    ¬ q ∣ v := by
  intro hv
  have hqg : q ∣ Nat.gcd u v := Nat.dvd_gcd hu hv
  rw [hG] at hqg
  have hle : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hqg
  exact (Nat.not_le_of_gt hq.1) hle

/--
Every odd prime dividing the raw Frey discriminant support divides at least
one of the three Beal bases.
-/
theorem xy_frey_odd_bad_prime_divides_a_or_b_or_c
    (r : ReducedPrimitiveCandidate)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hDelta : q ∣ XYFreyDiscriminantBeal
      r.a r.b r.c r.x r.y r.z) :
    q ∣ r.a ∨ q ∣ r.b ∨ q ∣ r.c := by
  have hfac :
      XYFreyDiscriminantBeal r.a r.b r.c r.x r.y r.z =
        16 * ((r.a ^ r.x) ^ 2 *
          ((r.b ^ r.y) ^ 2 * (r.c ^ r.z) ^ 2)) := by
    simp [XYFreyDiscriminantBeal, Nat.mul_assoc]
  rw [hfac] at hDelta
  rcases prime_dvd_mul_local hq hDelta with h16 | hrest
  · have hq2pow : q ∣ 2 ^ 4 := by simpa using h16
    have hqTwo : q ∣ 2 := prime_dvd_pow_reflect hq hq2pow
    have hqle : q ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < (2 : Nat)) hqTwo
    have hqge : 2 ≤ q := Nat.succ_le_of_lt hq.1
    have hEq : q = 2 := Nat.le_antisymm hqle hqge
    exact False.elim (hq2 hEq)
  · rcases prime_dvd_mul_local hq hrest with hA2 | hBC
    · have hAx : q ∣ r.a ^ r.x := prime_dvd_pow_reflect hq hA2
      exact Or.inl (prime_dvd_pow_reflect hq hAx)
    · rcases prime_dvd_mul_local hq hBC with hB2 | hC2
      · have hBy : q ∣ r.b ^ r.y := prime_dvd_pow_reflect hq hB2
        exact Or.inr (Or.inl (prime_dvd_pow_reflect hq hBy))
      · have hCz : q ∣ r.c ^ r.z := prime_dvd_pow_reflect hq hC2
        exact Or.inr (Or.inr (prime_dvd_pow_reflect hq hCz))

/--
Because the reduced candidate is pairwise primitive, every odd bad prime of
the Frey discriminant belongs to exactly one base support.
-/
theorem xy_frey_odd_bad_prime_exactly_one_base
    (r : ReducedPrimitiveCandidate)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hDelta : q ∣ XYFreyDiscriminantBeal
      r.a r.b r.c r.x r.y r.z) :
    (q ∣ r.a ∧ ¬ q ∣ r.b ∧ ¬ q ∣ r.c) ∨
    (q ∣ r.b ∧ ¬ q ∣ r.a ∧ ¬ q ∣ r.c) ∨
    (q ∣ r.c ∧ ¬ q ∣ r.a ∧ ¬ q ∣ r.b) := by
  rcases xy_frey_odd_bad_prime_divides_a_or_b_or_c r hq hq2 hDelta with
    ha | hb | hc
  ·
    have hnb := xyFrey_not_dvd_other_of_gcd_one hq ha (xyFrey_gcd_ab r)
    have hnc := xyFrey_not_dvd_other_of_gcd_one hq ha (xyFrey_gcd_ac r)
    exact Or.inl ⟨ha, hnb, hnc⟩
  ·
    have hna : ¬ q ∣ r.a := by
      intro ha
      exact (xyFrey_not_dvd_other_of_gcd_one hq ha (xyFrey_gcd_ab r)) hb
    have hnc := xyFrey_not_dvd_other_of_gcd_one hq hb (xyFrey_gcd_bc r)
    exact Or.inr (Or.inl ⟨hb, hna, hnc⟩)
  ·
    have hna : ¬ q ∣ r.a := by
      intro ha
      exact (xyFrey_not_dvd_other_of_gcd_one hq ha (xyFrey_gcd_ac r)) hc
    have hnb : ¬ q ∣ r.b := by
      intro hb
      exact (xyFrey_not_dvd_other_of_gcd_one hq hb (xyFrey_gcd_bc r)) hc
    exact Or.inr (Or.inr ⟨hc, hna, hnb⟩)

/-- Natural c4 kernel of the Frey model Y^2=X(X-a^x)(X+b^y). -/
def XYFreyC4Kernel
    (a b x y : Nat) : Nat :=
  16 * ((a ^ x) ^ 2 + (a ^ x) * (b ^ y) + (b ^ y) ^ 2)

private theorem xyFrey_dvd_mul_left
    {q u v : Nat}
    (h : q ∣ u) :
    q ∣ u * v := by
  rcases h with ⟨k, hk⟩
  refine ⟨k * v, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc]

private theorem xyFrey_dvd_mul_right
    {q u v : Nat}
    (h : q ∣ v) :
    q ∣ u * v := by
  rcases h with ⟨k, hk⟩
  refine ⟨u * k, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem xyFrey_dvd_add
    {q u v : Nat}
    (hu : q ∣ u)
    (hv : q ∣ v) :
    q ∣ u + v := by
  rcases hu with ⟨a, ha⟩
  rcases hv with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, Nat.mul_add]

/--
Every odd prime of the raw Frey discriminant is excluded from the c4 kernel.
This is the exact arithmetic input used by multiplicative-reduction theory.
-/
theorem xy_frey_odd_bad_prime_not_dvd_c4
    (r : ReducedPrimitiveCandidate)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hDelta : q ∣ XYFreyDiscriminantBeal
      r.a r.b r.c r.x r.y r.z) :
    ¬ q ∣ XYFreyC4Kernel r.a r.b r.x r.y := by
  intro hc4
  have h16not : ¬ q ∣ 16 := by
    intro h16
    have hq2pow : q ∣ 2 ^ 4 := by simpa using h16
    have hqTwo : q ∣ 2 := prime_dvd_pow_reflect hq hq2pow
    have hqle : q ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < (2 : Nat)) hqTwo
    have hqge : 2 ≤ q := Nat.succ_le_of_lt hq.1
    exact hq2 (Nat.le_antisymm hqle hqge)
  have hS :
      q ∣ (r.a ^ r.x) ^ 2 +
        (r.a ^ r.x) * (r.b ^ r.y) +
        (r.b ^ r.y) ^ 2 := by
    unfold XYFreyC4Kernel at hc4
    rcases prime_dvd_mul_local hq hc4 with h16 | hS
    · exact False.elim (h16not h16)
    · exact hS
  have hsupport :=
    xy_frey_odd_bad_prime_exactly_one_base r hq hq2 hDelta
  rcases hsupport with ha | hb | hc
  ·
    have hAx : q ∣ r.a ^ r.x :=
      dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) r.x_reduced.1) ha.1
    have hA2 : q ∣ (r.a ^ r.x) ^ 2 :=
      dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hAx
    have hAB : q ∣ (r.a ^ r.x) * (r.b ^ r.y) :=
      xyFrey_dvd_mul_left hAx
    have hfirst :
        q ∣ (r.a ^ r.x) ^ 2 +
          (r.a ^ r.x) * (r.b ^ r.y) :=
      xyFrey_dvd_add hA2 hAB
    have hB2 : q ∣ (r.b ^ r.y) ^ 2 := by
      have hs := Nat.dvd_sub hS hfirst
      have hdiff :
          ((r.a ^ r.x) ^ 2 +
              (r.a ^ r.x) * (r.b ^ r.y) +
              (r.b ^ r.y) ^ 2) -
            ((r.a ^ r.x) ^ 2 +
              (r.a ^ r.x) * (r.b ^ r.y)) =
            (r.b ^ r.y) ^ 2 := by
        omega
      rw [hdiff] at hs
      exact hs
    have hBy : q ∣ r.b ^ r.y :=
      prime_dvd_pow_reflect hq hB2
    have hB : q ∣ r.b :=
      prime_dvd_pow_reflect hq hBy
    exact ha.2.1 hB
  ·
    have hBy : q ∣ r.b ^ r.y :=
      dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) r.y_reduced.1) hb.1
    have hB2 : q ∣ (r.b ^ r.y) ^ 2 :=
      dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hBy
    have hAB : q ∣ (r.a ^ r.x) * (r.b ^ r.y) :=
      xyFrey_dvd_mul_right hBy
    have htail :
        q ∣ (r.a ^ r.x) * (r.b ^ r.y) +
          (r.b ^ r.y) ^ 2 :=
      xyFrey_dvd_add hAB hB2
    have hS' :
        q ∣ (r.a ^ r.x) ^ 2 +
          ((r.a ^ r.x) * (r.b ^ r.y) +
            (r.b ^ r.y) ^ 2) := by
      simpa [Nat.add_assoc] using hS
    have hA2 : q ∣ (r.a ^ r.x) ^ 2 := by
      have hs := Nat.dvd_sub hS' htail
      have hdiff :
          ((r.a ^ r.x) ^ 2 +
              ((r.a ^ r.x) * (r.b ^ r.y) +
                (r.b ^ r.y) ^ 2)) -
            ((r.a ^ r.x) * (r.b ^ r.y) +
              (r.b ^ r.y) ^ 2) =
            (r.a ^ r.x) ^ 2 := by
        omega
      rw [hdiff] at hs
      exact hs
    have hAx : q ∣ r.a ^ r.x :=
      prime_dvd_pow_reflect hq hA2
    have hA : q ∣ r.a :=
      prime_dvd_pow_reflect hq hAx
    exact hb.2.1 hA
  ·
    have hCz : q ∣ r.c ^ r.z :=
      dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) r.z_reduced.1) hc.1
    have hSum : q ∣ r.a ^ r.x + r.b ^ r.y := by
      rw [r.equation]
      exact hCz
    have hProd :
        q ∣ (r.a ^ r.x) * (r.a ^ r.x + r.b ^ r.y) :=
      xyFrey_dvd_mul_right hSum
    have hRewrite :
        (r.a ^ r.x) ^ 2 +
            (r.a ^ r.x) * (r.b ^ r.y) +
            (r.b ^ r.y) ^ 2 =
          (r.a ^ r.x) * (r.a ^ r.x + r.b ^ r.y) +
            (r.b ^ r.y) ^ 2 := by
      simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]
    have hS' :
        q ∣ (r.a ^ r.x) * (r.a ^ r.x + r.b ^ r.y) +
          (r.b ^ r.y) ^ 2 := by
      rw [← hRewrite]
      exact hS
    have hB2 : q ∣ (r.b ^ r.y) ^ 2 := by
      have hs := Nat.dvd_sub hS' hProd
      have hdiff :
          ((r.a ^ r.x) * (r.a ^ r.x + r.b ^ r.y) +
              (r.b ^ r.y) ^ 2) -
            ((r.a ^ r.x) * (r.a ^ r.x + r.b ^ r.y)) =
            (r.b ^ r.y) ^ 2 := by
        omega
      rw [hdiff] at hs
      exact hs
    have hBy : q ∣ r.b ^ r.y :=
      prime_dvd_pow_reflect hq hB2
    have hB : q ∣ r.b :=
      prime_dvd_pow_reflect hq hBy
    exact hc.2.2 hB

#print axioms MCore.BealEffective.OpenMath.xy_frey_discriminant_rewrite
#print axioms MCore.BealEffective.OpenMath.xy_four_frey_discriminant_normal_form
#print axioms MCore.BealEffective.OpenMath.xyFourPrimeFreyArithmeticPacket
#print axioms MCore.BealEffective.OpenMath.xy_frey_odd_bad_prime_divides_a_or_b_or_c
#print axioms MCore.BealEffective.OpenMath.xy_frey_odd_bad_prime_exactly_one_base
#print axioms MCore.BealEffective.OpenMath.xy_frey_odd_bad_prime_not_dvd_c4

end OpenMath
end BealEffective
end MCore
