import MCore.T20

namespace MCore

/-- Recursive quotient for the factorization c^n - b^n = (c-b)Q,
    expressed without integer subtraction on the powered terms. -/
def T21DiffQuot (c b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c ^ n + b * T21DiffQuot c b n

theorem T21_diff_factorization
    {b c : Nat} (hbc : b ≤ c) :
    ∀ n : Nat, b ^ n + (c - b) * T21DiffQuot c b n = c ^ n := by
  intro n
  induction n with
  | zero =>
      simp [T21DiffQuot]
  | succ n ih =>
      change b ^ (n + 1) + (c - b) * (c ^ n + b * T21DiffQuot c b n) = c ^ (n + 1)
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        b ^ n * b + (c - b) * (c ^ n + b * T21DiffQuot c b n)
            = b * (b ^ n + (c - b) * T21DiffQuot c b n) + (c - b) * c ^ n := by
                simp [Nat.left_distrib, Nat.right_distrib, Nat.mul_assoc,
                  Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]
        _ = b * c ^ n + (c - b) * c ^ n := by rw [ih]
        _ = (b + (c - b)) * c ^ n := by
              rw [Nat.add_mul]
        _ = c * c ^ n := by
              rw [Nat.add_comm b, Nat.sub_add_cancel hbc]
        _ = c ^ n * c := Nat.mul_comm _ _

theorem T21_right_same_exponent_gap
    {a b c x n : Nat}
    (ha : 0 < a)
    (heq : a ^ x + b ^ n = c ^ n) :
    b < c := by
  have hax : 0 < a ^ x := Nat.pow_pos ha
  have hp : b ^ n < c ^ n := by
    rw [← heq]
    exact Nat.lt_add_of_pos_left hax
  match Nat.lt_or_ge b c with
  | Or.inl h => exact h
  | Or.inr h =>
      have hpow : c ^ n ≤ b ^ n := Nat.pow_le_pow_left h n
      exact False.elim ((Nat.not_le_of_gt hp) hpow)

theorem T21_y_eq_z_gap_divides_a_power
    {a b c x y z : Nat}
    (ha : 0 < a)
    (heq : a ^ x + b ^ y = c ^ z)
    (hyz : y = z) :
    0 < c - b ∧ (c - b) ∣ a ^ x := by
  subst z
  have hbc_lt : b < c := T21_right_same_exponent_gap ha heq
  have hbc : b ≤ c := Nat.le_of_lt hbc_lt
  have hgap : 0 < c - b := Nat.zero_lt_sub_of_lt hbc_lt
  have hfac := T21_diff_factorization hbc y
  have hleft : b ^ y + a ^ x = c ^ y := by
    simpa [Nat.add_comm] using heq
  have hsum :
      b ^ y + a ^ x =
        b ^ y + (c - b) * T21DiffQuot c b y := by
    exact hleft.trans hfac.symm
  have hdivEq : a ^ x = (c - b) * T21DiffQuot c b y :=
    Nat.add_left_cancel hsum
  exact ⟨hgap, ⟨T21DiffQuot c b y, hdivEq⟩⟩

theorem T21_x_eq_z_gap_divides_b_power
    {a b c x y z : Nat}
    (hb : 0 < b)
    (heq : a ^ x + b ^ y = c ^ z)
    (hxz : x = z) :
    0 < c - a ∧ (c - a) ∣ b ^ y := by
  subst z
  have heq' : b ^ y + a ^ x = c ^ x := by
    simpa [Nat.add_comm] using heq
  have hac_lt : a < c := T21_right_same_exponent_gap hb heq'
  have hac : a ≤ c := Nat.le_of_lt hac_lt
  have hgap : 0 < c - a := Nat.zero_lt_sub_of_lt hac_lt
  have hfac := T21_diff_factorization hac x
  have hsum :
      a ^ x + b ^ y =
        a ^ x + (c - a) * T21DiffQuot c a x := by
    exact heq.trans hfac.symm
  have hdivEq : b ^ y = (c - a) * T21DiffQuot c a x :=
    Nat.add_left_cancel hsum
  exact ⟨hgap, ⟨T21DiffQuot c a x, hdivEq⟩⟩

def T21EqualExponentFactorConstraint (a b c x y z : Nat) : Prop :=
  (y = z → 0 < c - b ∧ (c - b) ∣ a ^ x) ∧
  (x = z → 0 < c - a ∧ (c - a) ∣ b ^ y)

def T21EqualExponentFactorCandidate : Prop :=
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
    T21EqualExponentFactorConstraint a b c x y z

theorem T21_T20_to_equal_exponent_factor :
    T20TwoAdicDepthCandidate → T21EqualExponentFactorCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, ?_⟩
  constructor
  · intro hyz
    exact T21_y_eq_z_gap_divides_a_power ha heq hyz
  · intro hxz
    exact T21_x_eq_z_gap_divides_b_power hb heq hxz

theorem T21_equal_exponent_factor_to_T20 :
    T21EqualExponentFactorCandidate → T20TwoAdicDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20⟩

theorem T21_candidate_iff_equal_exponent_factor :
    T20TwoAdicDepthCandidate ↔ T21EqualExponentFactorCandidate :=
  ⟨T21_T20_to_equal_exponent_factor, T21_equal_exponent_factor_to_T20⟩

def T21EqualExponentFactorScientificFrontier : Prop :=
  ¬ T21EqualExponentFactorCandidate

theorem T21_beal_iff_equal_exponent_factor_frontier :
    BealConjecture ↔ T21EqualExponentFactorScientificFrontier := by
  rw [T20_beal_iff_two_adic_depth_frontier]
  unfold T20TwoAdicDepthScientificFrontier T21EqualExponentFactorScientificFrontier
  exact not_congr T21_candidate_iff_equal_exponent_factor

#print axioms MCore.T21_diff_factorization
#print axioms MCore.T21_right_same_exponent_gap
#print axioms MCore.T21_y_eq_z_gap_divides_a_power
#print axioms MCore.T21_x_eq_z_gap_divides_b_power
#print axioms MCore.T21_candidate_iff_equal_exponent_factor
#print axioms MCore.T21_beal_iff_equal_exponent_factor_frontier

end MCore
