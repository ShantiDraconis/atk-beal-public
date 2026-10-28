import MCore.T12

namespace MCore

theorem T13_odd_representation
    {a : Nat} (ha : T12Odd a) :
    ∃ k : Nat, a = 2 * k + 1 := by
  refine ⟨a / 2, ?_⟩
  have h := Nat.mod_add_div a 2
  unfold T12Odd at ha
  rw [ha] at h
  calc
    a = 1 + 2 * (a / 2) := h.symm
    _ = 2 * (a / 2) + 1 := Nat.add_comm _ _

theorem T13_odd_mod_four
    {a : Nat} (ha : T12Odd a) :
    a % 4 = 1 ∨ a % 4 = 3 := by
  rcases T13_odd_representation ha with ⟨k, hak⟩
  match T12EvenDecidable k with
  | isTrue hk =>
      rcases hk with ⟨m, hkm⟩
      left
      have hform : 2 * (2 * m) + 1 = m * 4 + 1 := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [hak, hkm, hform]
      simp [Nat.add_mod, Nat.mul_mod]
  | isFalse hk =>
      have hko : T12Odd k := (T12_not_even_iff_odd k).mp hk
      rcases T13_odd_representation hko with ⟨m, hkm⟩
      right
      have hform : 2 * (2 * m + 1) + 1 = m * 4 + 3 := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
      rw [hak, hkm, hform]
      simp [Nat.add_mod, Nat.mul_mod]

theorem T13_odd_fourth_mod_four
    {a : Nat} (ha : T12Odd a) :
    a ^ 4 % 4 = 1 := by
  rcases T13_odd_mod_four ha with h1 | h3
  · simp [Nat.pow_succ, Nat.mul_mod, h1]
  · simp [Nat.pow_succ, Nat.mul_mod, h3]

theorem T13_even_pow_mod_four
    {c z : Nat} (hc : T12Even c) (hz : 2 < z) :
    c ^ z % 4 = 0 := by
  cases z with
  | zero =>
      exact False.elim (Nat.not_lt_zero 2 hz)
  | succ z =>
      cases z with
      | zero =>
          exact False.elim ((Nat.not_lt_of_ge (by decide : 1 ≤ 2)) hz)
      | succ z =>
          have hcc : 4 ∣ c * c := by
            have h22 : 2 * 2 ∣ c * c := Nat.mul_dvd_mul hc hc
            simpa using h22
          have hmul : 4 ∣ c ^ z * (c * c) :=
            Nat.dvd_mul_left_of_dvd hcc (c ^ z)
          apply Nat.mod_eq_zero_of_dvd
          simpa [Nat.pow_succ, Nat.mul_assoc] using hmul

/-- If C is the unique even base, the two left exponents cannot both be 4. -/
theorem T13_c_even_excludes_double_four
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c) :
    ¬ (x = 4 ∧ y = 4) := by
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
  intro h44
  rcases h44 with ⟨rfl, rfl⟩
  have ha4 : a ^ 4 % 4 = 1 := T13_odd_fourth_mod_four hoa
  have hb4 : b ^ 4 % 4 = 1 := T13_odd_fourth_mod_four hob
  have hc4 : c ^ z % 4 = 0 := T13_even_pow_mod_four hc hz.1
  have hmod := congrArg (fun n : Nat => n % 4) heq
  change (a ^ 4 + b ^ 4) % 4 = c ^ z % 4 at hmod
  have hleft : (a ^ 4 + b ^ 4) % 4 = 2 := by
    rw [Nat.add_mod, ha4, hb4]
  rw [hleft, hc4] at hmod
  exact (by decide : (2 : Nat) ≠ 0) hmod

/-- T13 residual adds the first nontrivial exponent/parity exclusion. -/
def T13ModularReducedCandidate : Prop :=
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
    (T12Even c → ¬ (x = 4 ∧ y = 4))

theorem T13_T12_to_modular :
    T12ParityReducedCandidate → T13ModularReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    fun hce => T13_c_even_excludes_double_four hx hy hz heq hpar hce⟩

theorem T13_modular_to_T12 :
    T13ModularReducedCandidate → T12ParityReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar⟩

theorem T13_candidate_iff_modular :
    T12ParityReducedCandidate ↔ T13ModularReducedCandidate :=
  ⟨T13_T12_to_modular, T13_modular_to_T12⟩

def T13ModularScientificFrontier : Prop :=
  ¬ T13ModularReducedCandidate

theorem T13_beal_iff_modular_frontier :
    BealConjecture ↔ T13ModularScientificFrontier := by
  rw [T12_beal_iff_parity_frontier]
  unfold T12ParityScientificFrontier T13ModularScientificFrontier
  exact not_congr T13_candidate_iff_modular

#print axioms MCore.T13_odd_representation
#print axioms MCore.T13_odd_mod_four
#print axioms MCore.T13_odd_fourth_mod_four
#print axioms MCore.T13_even_pow_mod_four
#print axioms MCore.T13_c_even_excludes_double_four
#print axioms MCore.T13_candidate_iff_modular
#print axioms MCore.T13_beal_iff_modular_frontier

end MCore
