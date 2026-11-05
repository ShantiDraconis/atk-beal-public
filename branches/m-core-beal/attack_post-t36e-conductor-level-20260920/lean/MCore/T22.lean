import MCore.T21

namespace MCore

/-- Parity of the equal-exponent difference quotient. For odd endpoints,
    the quotient has the same parity as the exponent. -/
theorem T22_diff_quot_mod_two
    {b c : Nat} (hb : T12Odd b) (hc : T12Odd c) :
    ∀ n : Nat, T21DiffQuot c b n % 2 = n % 2 := by
  intro n
  induction n with
  | zero =>
      simp [T21DiffQuot]
  | succ n ih =>
      change (c ^ n + b * T21DiffQuot c b n) % 2 = (n + 1) % 2
      rw [Nat.add_mod, Nat.mul_mod, T12_odd_pow_mod_two hc, hb, ih, Nat.add_mod]
      simp [Nat.add_comm]

theorem T22_diff_quot_odd
    {b c n : Nat}
    (hb : T12Odd b) (hc : T12Odd c) (hn : T12Odd n) :
    T12Odd (T21DiffQuot c b n) := by
  unfold T12Odd
  exact (T22_diff_quot_mod_two hb hc n).trans hn

/-- Multiplication by an odd factor does not create powers of two.
    This is the elementary cancellation kernel needed for the LTE-like step. -/
theorem T22_two_pow_dvd_mul_odd_left
    {d q : Nat} (hq : T12Odd q) :
    ∀ r : Nat, 2 ^ r ∣ d * q → 2 ^ r ∣ d := by
  intro r
  induction r generalizing d with
  | zero =>
      intro _
      simp
  | succ r ih =>
      intro hpow
      have h2pow : 2 ∣ 2 ^ (r + 1) := by
        refine ⟨2 ^ r, ?_⟩
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      have h2prod : 2 ∣ d * q := nat_dvd_trans h2pow hpow
      have hdEven : T12Even d := by
        match T12EvenDecidable d with
        | isTrue hd =>
            exact hd
        | isFalse hd =>
            have hod : T12Odd d := (T12_not_even_iff_odd d).mp hd
            have hoddprod : (d * q) % 2 = 1 := by
              rw [Nat.mul_mod, hod, hq]
            have hzero : (d * q) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2prod
            rw [hoddprod] at hzero
            exact False.elim (Nat.one_ne_zero hzero)
      rcases hdEven with ⟨d1, hd1⟩
      rcases hpow with ⟨k, hk⟩
      have hcancel : d1 * q = 2 ^ r * k := by
        have htwo :
            2 * (d1 * q) = 2 * (2 ^ r * k) := by
          calc
            2 * (d1 * q) = (2 * d1) * q := by
              simp [Nat.mul_assoc]
            _ = d * q := by rw [← hd1]
            _ = 2 ^ (r + 1) * k := hk
            _ = 2 * (2 ^ r * k) := by
              rw [Nat.pow_succ]
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (2 : Nat)) htwo
      have hd1pow : 2 ^ r ∣ d1 * q := ⟨k, hcancel⟩
      have hd1div : 2 ^ r ∣ d1 := ih hd1pow
      rcases hd1div with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [hd1, hm, Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem T22_two_pow_dvd_mul_odd_iff_left
    {d q r : Nat} (hq : T12Odd q) :
    2 ^ r ∣ d * q ↔ 2 ^ r ∣ d := by
  constructor
  · exact T22_two_pow_dvd_mul_odd_left hq r
  · intro hd
    rcases hd with ⟨k, hk⟩
    refine ⟨k * q, ?_⟩
    rw [hk]
    simp [Nat.mul_assoc]

theorem T22_y_eq_z_exact_factor
    {a b c x y z : Nat}
    (ha : 0 < a)
    (heq : a ^ x + b ^ y = c ^ z)
    (hyz : y = z) :
    a ^ x = (c - b) * T21DiffQuot c b y := by
  subst z
  have hbc_lt : b < c := T21_right_same_exponent_gap ha heq
  have hbc : b ≤ c := Nat.le_of_lt hbc_lt
  have hfac := T21_diff_factorization hbc y
  have hleft : b ^ y + a ^ x = c ^ y := by
    simpa [Nat.add_comm] using heq
  have hsum :
      b ^ y + a ^ x =
        b ^ y + (c - b) * T21DiffQuot c b y :=
    hleft.trans hfac.symm
  exact Nat.add_left_cancel hsum

theorem T22_x_eq_z_exact_factor
    {a b c x y z : Nat}
    (hb : 0 < b)
    (heq : a ^ x + b ^ y = c ^ z)
    (hxz : x = z) :
    b ^ y = (c - a) * T21DiffQuot c a x := by
  subst z
  have heq' : b ^ y + a ^ x = c ^ x := by
    simpa [Nat.add_comm] using heq
  have hac_lt : a < c := T21_right_same_exponent_gap hb heq'
  have hac : a ≤ c := Nat.le_of_lt hac_lt
  have hfac := T21_diff_factorization hac x
  have hsum :
      a ^ x + b ^ y =
        a ^ x + (c - a) * T21DiffQuot c a x :=
    heq.trans hfac.symm
  exact Nat.add_left_cancel hsum

/-- Elementary LTE-like exactness for the A-even, y=z odd branch:
    every power of two dividing A^x divides exactly the base gap C-B, and
    conversely. -/
theorem T22_a_even_equal_odd_exponent_two_adic_exact
    {a b c x y z r : Nat}
    (haPos : 0 < a)
    (hy : T7ReducedExponent y)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (haEven : T12Even a)
    (hyz : y = z)
    (hyne4 : y ≠ 4) :
    (2 ^ r ∣ a ^ x ↔ 2 ^ r ∣ c - b) := by
  rcases T18_a_even_other_odd hpar haEven with ⟨hob, hoc⟩
  have hoy : T12Odd y := T17_reduced_ne_four_odd hy hyne4
  have hqodd : T12Odd (T21DiffQuot c b y) :=
    T22_diff_quot_odd hob hoc hoy
  have hfactor :
      a ^ x = (c - b) * T21DiffQuot c b y :=
    T22_y_eq_z_exact_factor haPos heq hyz
  rw [hfactor]
  exact T22_two_pow_dvd_mul_odd_iff_left hqodd

/-- Symmetric exactness for the B-even, x=z odd branch. -/
theorem T22_b_even_equal_odd_exponent_two_adic_exact
    {a b c x y z r : Nat}
    (hbPos : 0 < b)
    (hx : T7ReducedExponent x)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hbEven : T12Even b)
    (hxz : x = z)
    (hxne4 : x ≠ 4) :
    (2 ^ r ∣ b ^ y ↔ 2 ^ r ∣ c - a) := by
  rcases T18_b_even_other_odd hpar hbEven with ⟨hoa, hoc⟩
  have hox : T12Odd x := T17_reduced_ne_four_odd hx hxne4
  have hqodd : T12Odd (T21DiffQuot c a x) :=
    T22_diff_quot_odd hoa hoc hox
  have hfactor :
      b ^ y = (c - a) * T21DiffQuot c a x :=
    T22_x_eq_z_exact_factor hbPos heq hxz
  rw [hfactor]
  exact T22_two_pow_dvd_mul_odd_iff_left hqodd

def T22EqualOddExponentTwoAdicConstraint (a b c x y z : Nat) : Prop :=
  (T12Even a → y = z → y ≠ 4 →
    ∀ r : Nat, (2 ^ r ∣ a ^ x ↔ 2 ^ r ∣ c - b)) ∧
  (T12Even b → x = z → x ≠ 4 →
    ∀ r : Nat, (2 ^ r ∣ b ^ y ↔ 2 ^ r ∣ c - a))

def T22EqualOddExponentTwoAdicCandidate : Prop :=
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
    T22EqualOddExponentTwoAdicConstraint a b c x y z

theorem T22_T21_to_two_adic_exact :
    T21EqualExponentFactorCandidate → T22EqualOddExponentTwoAdicCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, ?_⟩
  constructor
  · intro hae hyz hyne4 r
    exact T22_a_even_equal_odd_exponent_two_adic_exact
      ha hy heq hpar hae hyz hyne4
  · intro hbe hxz hxne4 r
    exact T22_b_even_equal_odd_exponent_two_adic_exact
      hb hx heq hpar hbe hxz hxne4

theorem T22_two_adic_exact_to_T21 :
    T22EqualOddExponentTwoAdicCandidate → T21EqualExponentFactorCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21⟩

theorem T22_candidate_iff_two_adic_exact :
    T21EqualExponentFactorCandidate ↔ T22EqualOddExponentTwoAdicCandidate :=
  ⟨T22_T21_to_two_adic_exact, T22_two_adic_exact_to_T21⟩

def T22EqualOddExponentTwoAdicScientificFrontier : Prop :=
  ¬ T22EqualOddExponentTwoAdicCandidate

theorem T22_beal_iff_equal_odd_exponent_two_adic_frontier :
    BealConjecture ↔ T22EqualOddExponentTwoAdicScientificFrontier := by
  rw [T21_beal_iff_equal_exponent_factor_frontier]
  unfold T21EqualExponentFactorScientificFrontier
    T22EqualOddExponentTwoAdicScientificFrontier
  exact not_congr T22_candidate_iff_two_adic_exact

#print axioms MCore.T22_diff_quot_mod_two
#print axioms MCore.T22_diff_quot_odd
#print axioms MCore.T22_two_pow_dvd_mul_odd_left
#print axioms MCore.T22_two_pow_dvd_mul_odd_iff_left
#print axioms MCore.T22_a_even_equal_odd_exponent_two_adic_exact
#print axioms MCore.T22_b_even_equal_odd_exponent_two_adic_exact
#print axioms MCore.T22_candidate_iff_two_adic_exact
#print axioms MCore.T22_beal_iff_equal_odd_exponent_two_adic_frontier

end MCore
