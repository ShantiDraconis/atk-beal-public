import MCore.T31

namespace MCore

/-- Natural-number kernel for the c4 invariant of the Frey model
    Y^2 = X (X - A^x) (X + B^y):
    c4 = 16 * (A^(2x) + A^x B^y + B^(2y)).
    T32 uses only this exact positive expression. -/
def T32FreyC4Kernel (a b x y : Nat) : Nat :=
  16 * ((a ^ x) ^ 2 + (a ^ x) * (b ^ y) + (b ^ y) ^ 2)

theorem T32_dvd_mul_of_dvd_left
    {p u v : Nat} (h : p ∣ u) : p ∣ u * v := by
  rcases h with ⟨k, hk⟩
  refine ⟨k * v, ?_⟩
  calc
    u * v = (p * k) * v := congrArg (fun t : Nat => t * v) hk
    _ = p * (k * v) := Nat.mul_assoc p k v

theorem T32_dvd_mul_of_dvd_right
    {p u v : Nat} (h : p ∣ v) : p ∣ u * v := by
  rcases h with ⟨k, hk⟩
  refine ⟨u * k, ?_⟩
  calc
    u * v = u * (p * k) := congrArg (fun t : Nat => u * t) hk
    _ = (u * p) * k := (Nat.mul_assoc u p k).symm
    _ = (p * u) * k := congrArg (fun t : Nat => t * k) (Nat.mul_comm u p)
    _ = p * (u * k) := Nat.mul_assoc p u k

theorem T32_quadratic_decompose (X Y : Nat) :
    X ^ 2 + X * Y + Y ^ 2 = X * (X + Y) + Y ^ 2 := by
  simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]

/-- Pairwise primitiveness excludes an odd prime from simultaneously dividing
    the Frey discriminant and the c4 kernel. This is the arithmetic input
    preceding any claim about Kodaira type, minimality, or conductor. -/
theorem T32_no_odd_common_prime_delta_c4
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hp : IsPrime p) (hp2 : p ≠ 2)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    ¬ p ∣ T32FreyC4Kernel a b x y := by
  intro hc4
  have hS :
      p ∣ (a ^ x) ^ 2 + (a ^ x) * (b ^ y) + (b ^ y) ^ 2 := by
    unfold T32FreyC4Kernel at hc4
    rcases T29_prime_dvd_mul hp hc4 with h16 | hS
    · exact False.elim (hp2 (T31_prime_dvd_sixteen_eq_two hp h16))
    · exact hS
  rcases T31_frey_radical_prime_support hx hy hz hp hDelta with hpEq | hpa | hpb | hpc
  · exact False.elim (hp2 hpEq)
  ·
    have hX : p ∣ a ^ x := T11_dvd_pow_of_dvd hx hpa
    have hX2 : p ∣ (a ^ x) ^ 2 :=
      T11_dvd_pow_of_dvd (by decide : 0 < 2) hX
    have hXY : p ∣ (a ^ x) * (b ^ y) :=
      T32_dvd_mul_of_dvd_left hX
    have hU : p ∣ (a ^ x) ^ 2 + (a ^ x) * (b ^ y) :=
      T11_dvd_add hX2 hXY
    have hY2 : p ∣ (b ^ y) ^ 2 := by
      have hsub :=
        Nat.dvd_sub hS hU
      have hdiff :
          ((a ^ x) ^ 2 + (a ^ x) * (b ^ y) + (b ^ y) ^ 2) -
              ((a ^ x) ^ 2 + (a ^ x) * (b ^ y)) =
            (b ^ y) ^ 2 :=
        Nat.add_sub_cancel_left
          ((a ^ x) ^ 2 + (a ^ x) * (b ^ y))
          ((b ^ y) ^ 2)
      rw [hdiff] at hsub
      exact hsub
    have hpb' : p ∣ b :=
      T30_prime_dvd_power_square_to_base hp hy hY2
    exact hpw.1 ⟨p, hp.1, hpa, hpb'⟩
  ·
    have hY : p ∣ b ^ y := T11_dvd_pow_of_dvd hy hpb
    have hY2 : p ∣ (b ^ y) ^ 2 :=
      T11_dvd_pow_of_dvd (by decide : 0 < 2) hY
    have hXY : p ∣ (a ^ x) * (b ^ y) :=
      T32_dvd_mul_of_dvd_right hY
    have hV : p ∣ (a ^ x) * (b ^ y) + (b ^ y) ^ 2 :=
      T11_dvd_add hXY hY2
    have hS' :
        p ∣ (a ^ x) ^ 2 + ((a ^ x) * (b ^ y) + (b ^ y) ^ 2) := by
      simpa [Nat.add_assoc] using hS
    have hX2 : p ∣ (a ^ x) ^ 2 := by
      have hsub := Nat.dvd_sub hS' hV
      simpa using hsub
    have hpa' : p ∣ a :=
      T30_prime_dvd_power_square_to_base hp hx hX2
    exact hpw.1 ⟨p, hp.1, hpa', hpb⟩
  ·
    have hCz : p ∣ c ^ z := T11_dvd_pow_of_dvd hz hpc
    have hXYsum : p ∣ a ^ x + b ^ y := by
      rw [heq]
      exact hCz
    have hU : p ∣ (a ^ x) * (a ^ x + b ^ y) :=
      T32_dvd_mul_of_dvd_right hXYsum
    have hS' :
        p ∣ (a ^ x) * (a ^ x + b ^ y) + (b ^ y) ^ 2 := by
      rw [← T32_quadratic_decompose]
      exact hS
    have hY2 : p ∣ (b ^ y) ^ 2 := by
      have hsub := Nat.dvd_sub hS' hU
      have hdiff :
          ((a ^ x) * (a ^ x + b ^ y) + (b ^ y) ^ 2) -
              ((a ^ x) * (a ^ x + b ^ y)) =
            (b ^ y) ^ 2 :=
        Nat.add_sub_cancel_left
          ((a ^ x) * (a ^ x + b ^ y))
          ((b ^ y) ^ 2)
      rw [hdiff] at hsub
      exact hsub
    have hpb' : p ∣ b :=
      T30_prime_dvd_power_square_to_base hp hy hY2
    exact hpw.2.2 ⟨p, hp.1, hpb', hpc⟩

def T32FreyC4CoprimeConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat, IsPrime p → p ≠ 2 →
    p ∣ T24FreyDiscriminantBeal a b c x y z →
    ¬ p ∣ T32FreyC4Kernel a b x y

def T32FreyC4CoprimeCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c ∧
    T12ExactlyOneEven a b c ∧
    (T12Even c → ¬ (x = 4 ∧ y = 4)) ∧
    T14CResidueConstraint a b c x y z ∧
    T15CBaseResidueConstraint a b c x y z ∧
    T16CEightConstraint a b c x y z ∧
    T17CEvenClassifier a b c x y z ∧
    T18AEvenClassifier a b c x y z ∧
    T18BEvenClassifier a b c x y z ∧
    T19VariableTwoAdicConstraint a b c x y z ∧
    T20TwoAdicDepthConstraint a b c x y z ∧
    T21EqualExponentFactorConstraint a b c x y z ∧
    T22EqualOddExponentTwoAdicConstraint a b c x y z ∧
    T23EqualOddGapDepthConstraint a b c x y z ∧
    T24FreyDiscriminantConstraint a b c x y z ∧
    T25FreyTwoAdicDepthConstraint a b c x y z ∧
    T27FreyDivisorDepthConstraint a b c x y z ∧
    T28FreyPrimeSupportConstraint a b c x y z ∧
    T30FreyBasePrimeSupportConstraint a b c x y z ∧
    T31FreyRadicalSupportConstraint a b c x y z ∧
    T32FreyC4CoprimeConstraint a b c x y z

theorem T32_T31_to_c4_coprime :
    T31FreyRadicalSupportCandidate → T32FreyC4CoprimeCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, ?_⟩
  intro p hp hp2 hDelta
  exact T32_no_odd_common_prime_delta_c4 hx0 hy0 hz0 heq hpw hp hp2 hDelta

theorem T32_c4_coprime_to_T31 :
    T32FreyC4CoprimeCandidate → T31FreyRadicalSupportCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31⟩

theorem T32_candidate_iff_c4_coprime :
    T31FreyRadicalSupportCandidate ↔ T32FreyC4CoprimeCandidate :=
  ⟨T32_T31_to_c4_coprime, T32_c4_coprime_to_T31⟩

def T32FreyC4CoprimeScientificFrontier : Prop :=
  ¬ T32FreyC4CoprimeCandidate

theorem T32_beal_iff_c4_coprime_frontier :
    BealConjecture ↔ T32FreyC4CoprimeScientificFrontier := by
  rw [T31_beal_iff_radical_support_frontier]
  unfold T31FreyRadicalSupportScientificFrontier
    T32FreyC4CoprimeScientificFrontier
  exact not_congr T32_candidate_iff_c4_coprime

#print axioms MCore.T32_quadratic_decompose
#print axioms MCore.T32_no_odd_common_prime_delta_c4
#print axioms MCore.T32_candidate_iff_c4_coprime
#print axioms MCore.T32_beal_iff_c4_coprime_frontier

end MCore
