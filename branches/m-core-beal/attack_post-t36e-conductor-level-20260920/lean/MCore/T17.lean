import MCore.T16

namespace MCore

theorem T17_one_mod_eight_pow
    {u k : Nat} (hu : u % 8 = 1) :
    u ^ k % 8 = 1 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hu]

/-- An odd base raised to an odd exponent preserves its residue modulo eight. -/
theorem T17_odd_pow_mod_eight_eq_base
    {a n : Nat} (ha : T12Odd a) (hn : T12Odd n) :
    a ^ n % 8 = a % 8 := by
  rcases T13_odd_representation hn with ⟨k, hnk⟩
  have ha2 : a ^ 2 % 8 = 1 := T16_odd_square_mod_eight ha
  have hblock : (a ^ 2) ^ k % 8 = 1 :=
    T17_one_mod_eight_pow ha2
  have houter : (a ^ 2) ^ k = a ^ (2 * k) :=
    T10_pow_mul_outer a 2 k
  have h2k : a ^ (2 * k) % 8 = 1 := by
    rw [← houter]
    exact hblock
  rw [hnk, T10_pow_add a (2 * k) 1, Nat.mul_mod, h2k]
  simp

theorem T17_reduced_ne_four_odd
    {n : Nat} (hn : T7ReducedExponent n) (hne : n ≠ 4) :
    T12Odd n := by
  rcases hn.2 with h4 | hp
  · exact False.elim (hne h4)
  · exact T15_prime_gt_two_odd hp hn.1

theorem T17_c_even_left_four_forces_right_base_seven
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hx4 : x = 4) :
    b % 8 = 7 := by
  have hnot44 : ¬ (x = 4 ∧ y = 4) :=
    T13_c_even_excludes_double_four hx hy hz heq hpar hc
  have hyne4 : y ≠ 4 := by
    intro hy4
    exact hnot44 ⟨hx4, hy4⟩
  have hoy : T12Odd y := T17_reduced_ne_four_odd hy hyne4
  have hnb : ¬ T12Even b := by
    rcases hpar with ha | hb | hcOnly
    · exact ha.2.1
    · exact False.elim (hb.2.2 hc)
    · exact hcOnly.2.1
  have hob : T12Odd b := (T12_not_even_iff_odd b).mp hnb
  have hpow : b ^ y % 8 = 7 :=
    T16_c_even_left_four_forces_right_seven hz heq hpar hc hx4
  have hbase : b ^ y % 8 = b % 8 :=
    T17_odd_pow_mod_eight_eq_base hob hoy
  calc
    b % 8 = b ^ y % 8 := hbase.symm
    _ = 7 := hpow

theorem T17_c_even_right_four_forces_left_base_seven
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hy4 : y = 4) :
    a % 8 = 7 := by
  have hnot44 : ¬ (x = 4 ∧ y = 4) :=
    T13_c_even_excludes_double_four hx hy hz heq hpar hc
  have hxne4 : x ≠ 4 := by
    intro hx4
    exact hnot44 ⟨hx4, hy4⟩
  have hox : T12Odd x := T17_reduced_ne_four_odd hx hxne4
  have hna : ¬ T12Even a := by
    rcases hpar with ha | hb | hcOnly
    · exact False.elim (ha.2.2 hc)
    · exact hb.1
    · exact hcOnly.1
  have hoa : T12Odd a := (T12_not_even_iff_odd a).mp hna
  have hpow : a ^ x % 8 = 7 :=
    T16_c_even_right_four_forces_left_seven hz heq hpar hc hy4
  have hbase : a ^ x % 8 = a % 8 :=
    T17_odd_pow_mod_eight_eq_base hoa hox
  calc
    a % 8 = a ^ x % 8 := hbase.symm
    _ = 7 := hpow

theorem T17_c_even_odd_odd_sum_zero
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hxne4 : x ≠ 4)
    (hyne4 : y ≠ 4) :
    (a + b) % 8 = 0 := by
  have hna : ¬ T12Even a := by
    rcases hpar with ha | hb | hcOnly
    · exact False.elim (ha.2.2 hc)
    · exact hb.1
    · exact hcOnly.1
  have hnb : ¬ T12Even b := by
    rcases hpar with ha | hb | hcOnly
    · exact ha.2.1
    · exact False.elim (hb.2.2 hc)
    · exact hcOnly.2.1
  have hoa : T12Odd a := (T12_not_even_iff_odd a).mp hna
  have hob : T12Odd b := (T12_not_even_iff_odd b).mp hnb
  have hox : T12Odd x := T17_reduced_ne_four_odd hx hxne4
  have hoy : T12Odd y := T17_reduced_ne_four_odd hy hyne4
  have hax : a ^ x % 8 = a % 8 := T17_odd_pow_mod_eight_eq_base hoa hox
  have hby : b ^ y % 8 = b % 8 := T17_odd_pow_mod_eight_eq_base hob hoy
  have hcz : c ^ z % 8 = 0 := T16_even_pow_mod_eight hc hz.1
  have hmod := congrArg (fun n : Nat => n % 8) heq
  change (a ^ x + b ^ y) % 8 = c ^ z % 8 at hmod
  rw [Nat.add_mod, hax, hby, hcz] at hmod
  rw [Nat.add_mod]
  exact hmod

def T17CEvenClassifier (a b c x y z : Nat) : Prop :=
  T12Even c →
    (x = 4 → b % 8 = 7) ∧
    (y = 4 → a % 8 = 7) ∧
    (x ≠ 4 → y ≠ 4 → (a + b) % 8 = 0)

def T17ClassifiedReducedCandidate : Prop :=
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
    T17CEvenClassifier a b c x y z

theorem T17_T16_to_classified :
    T16EightReducedCandidate → T17ClassifiedReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, ?_⟩
  intro hce
  constructor
  · intro hx4
    exact T17_c_even_left_four_forces_right_base_seven hx hy hz heq hpar hce hx4
  constructor
  · intro hy4
    exact T17_c_even_right_four_forces_left_base_seven hx hy hz heq hpar hce hy4
  · intro hxne4 hyne4
    exact T17_c_even_odd_odd_sum_zero hx hy hz heq hpar hce hxne4 hyne4

theorem T17_classified_to_T16 :
    T17ClassifiedReducedCandidate → T16EightReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16⟩

theorem T17_candidate_iff_classified :
    T16EightReducedCandidate ↔ T17ClassifiedReducedCandidate :=
  ⟨T17_T16_to_classified, T17_classified_to_T16⟩

def T17ClassifiedScientificFrontier : Prop :=
  ¬ T17ClassifiedReducedCandidate

theorem T17_beal_iff_classified_frontier :
    BealConjecture ↔ T17ClassifiedScientificFrontier := by
  rw [T16_beal_iff_eight_frontier]
  unfold T16EightScientificFrontier T17ClassifiedScientificFrontier
  exact not_congr T17_candidate_iff_classified

#print axioms MCore.T17_odd_pow_mod_eight_eq_base
#print axioms MCore.T17_reduced_ne_four_odd
#print axioms MCore.T17_c_even_left_four_forces_right_base_seven
#print axioms MCore.T17_c_even_right_four_forces_left_base_seven
#print axioms MCore.T17_c_even_odd_odd_sum_zero
#print axioms MCore.T17_candidate_iff_classified
#print axioms MCore.T17_beal_iff_classified_frontier

end MCore
