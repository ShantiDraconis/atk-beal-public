import MCore.T14

namespace MCore

theorem T15_odd_square_mod_four
    {a : Nat} (ha : T12Odd a) :
    a ^ 2 % 4 = 1 := by
  rcases T13_odd_mod_four ha with h1 | h3
  · simp [Nat.pow_succ, Nat.mul_mod, h1]
  · simp [Nat.pow_succ, Nat.mul_mod, h3]

theorem T15_one_mod_four_pow
    {u k : Nat} (hu : u % 4 = 1) :
    u ^ k % 4 = 1 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hu]

/-- An odd base raised to an odd exponent has the same residue modulo four. -/
theorem T15_odd_pow_mod_four_eq_base
    {a n : Nat} (ha : T12Odd a) (hn : T12Odd n) :
    a ^ n % 4 = a % 4 := by
  rcases T13_odd_representation hn with ⟨k, hnk⟩
  have ha2 : a ^ 2 % 4 = 1 := T15_odd_square_mod_four ha
  have hblock : (a ^ 2) ^ k % 4 = 1 :=
    T15_one_mod_four_pow ha2
  have houter : (a ^ 2) ^ k = a ^ (2 * k) :=
    T10_pow_mul_outer a 2 k
  have h2k : a ^ (2 * k) % 4 = 1 := by
    rw [← houter]
    exact hblock
  rw [hnk, T10_pow_add a (2 * k) 1, Nat.mul_mod, h2k]
  simp

/-- A prime strictly above two is odd, using only the local elementary
    divisor definition of prime. -/
theorem T15_prime_gt_two_odd
    {p : Nat} (hp : IsPrime p) (h2p : 2 < p) :
    T12Odd p := by
  apply (T12_not_even_iff_odd p).mp
  intro heven
  rcases hp.2 2 heven with h21 | h2eq
  · exact (by decide : (2 : Nat) ≠ 1) h21
  · exact (Nat.ne_of_lt h2p) h2eq

theorem T15_c_even_left_four_forces_right_base_three
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hx4 : x = 4) :
    b % 4 = 3 := by
  have hnot44 : ¬ (x = 4 ∧ y = 4) :=
    T13_c_even_excludes_double_four hx hy hz heq hpar hc
  have hyne4 : y ≠ 4 := by
    intro hy4
    exact hnot44 ⟨hx4, hy4⟩
  have hyp : IsPrime y := by
    rcases hy.2 with hy4 | hp
    · exact False.elim (hyne4 hy4)
    · exact hp
  have hoy : T12Odd y := T15_prime_gt_two_odd hyp hy.1
  have hnb : ¬ T12Even b := by
    rcases hpar with ha | hb | hcOnly
    · exact ha.2.1
    · exact False.elim (hb.2.2 hc)
    · exact hcOnly.2.1
  have hob : T12Odd b := (T12_not_even_iff_odd b).mp hnb
  have hpow : b ^ y % 4 = 3 :=
    T14_c_even_left_four_forces_right_three hz heq hpar hc hx4
  have hbase : b ^ y % 4 = b % 4 :=
    T15_odd_pow_mod_four_eq_base hob hoy
  calc
    b % 4 = b ^ y % 4 := hbase.symm
    _ = 3 := hpow

theorem T15_c_even_right_four_forces_left_base_three
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hy4 : y = 4) :
    a % 4 = 3 := by
  have hnot44 : ¬ (x = 4 ∧ y = 4) :=
    T13_c_even_excludes_double_four hx hy hz heq hpar hc
  have hxne4 : x ≠ 4 := by
    intro hx4
    exact hnot44 ⟨hx4, hy4⟩
  have hxp : IsPrime x := by
    rcases hx.2 with hx4 | hp
    · exact False.elim (hxne4 hx4)
    · exact hp
  have hox : T12Odd x := T15_prime_gt_two_odd hxp hx.1
  have hna : ¬ T12Even a := by
    rcases hpar with ha | hb | hcOnly
    · exact False.elim (ha.2.2 hc)
    · exact hb.1
    · exact hcOnly.1
  have hoa : T12Odd a := (T12_not_even_iff_odd a).mp hna
  have hpow : a ^ x % 4 = 3 :=
    T14_c_even_right_four_forces_left_three hz heq hpar hc hy4
  have hbase : a ^ x % 4 = a % 4 :=
    T15_odd_pow_mod_four_eq_base hoa hox
  calc
    a % 4 = a ^ x % 4 := hbase.symm
    _ = 3 := hpow

def T15CBaseResidueConstraint (a b c x y z : Nat) : Prop :=
  T12Even c →
    (x = 4 → b % 4 = 3) ∧
    (y = 4 → a % 4 = 3)

def T15BaseResidueReducedCandidate : Prop :=
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
    T15CBaseResidueConstraint a b c x y z

theorem T15_T14_to_base_residue :
    T14ResidueReducedCandidate → T15BaseResidueReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44, h14⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44, h14, ?_⟩
  intro hce
  constructor
  · intro hx4
    exact T15_c_even_left_four_forces_right_base_three hx hy hz heq hpar hce hx4
  · intro hy4
    exact T15_c_even_right_four_forces_left_base_three hx hy hz heq hpar hce hy4

theorem T15_base_residue_to_T14 :
    T15BaseResidueReducedCandidate → T14ResidueReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44, h14, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44, h14⟩

theorem T15_candidate_iff_base_residue :
    T14ResidueReducedCandidate ↔ T15BaseResidueReducedCandidate :=
  ⟨T15_T14_to_base_residue, T15_base_residue_to_T14⟩

def T15BaseResidueScientificFrontier : Prop :=
  ¬ T15BaseResidueReducedCandidate

theorem T15_beal_iff_base_residue_frontier :
    BealConjecture ↔ T15BaseResidueScientificFrontier := by
  rw [T14_beal_iff_residue_frontier]
  unfold T14ResidueScientificFrontier T15BaseResidueScientificFrontier
  exact not_congr T15_candidate_iff_base_residue

#print axioms MCore.T15_odd_square_mod_four
#print axioms MCore.T15_one_mod_four_pow
#print axioms MCore.T15_odd_pow_mod_four_eq_base
#print axioms MCore.T15_prime_gt_two_odd
#print axioms MCore.T15_c_even_left_four_forces_right_base_three
#print axioms MCore.T15_c_even_right_four_forces_left_base_three
#print axioms MCore.T15_candidate_iff_base_residue
#print axioms MCore.T15_beal_iff_base_residue_frontier

end MCore
