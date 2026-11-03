import MCore.T13

namespace MCore

/-- Under the surviving C-even branch, a fourth power on the left forces the
    opposite powered term into residue 3 modulo 4. This is strictly sharper
    residue data than the T13 exclusion of the double-four case. -/
theorem T14_c_even_left_four_forces_right_three
    {a b c x y z : Nat}
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hx4 : x = 4) :
    b ^ y % 4 = 3 := by
  have hna : ¬ T12Even a := by
    rcases hpar with ha | hb | hcOnly
    · exact False.elim (ha.2.2 hc)
    · exact hb.1
    · exact hcOnly.1
  have hoa : T12Odd a := (T12_not_even_iff_odd a).mp hna
  subst x
  have ha4 : a ^ 4 % 4 = 1 := T13_odd_fourth_mod_four hoa
  have hc4 : c ^ z % 4 = 0 := T13_even_pow_mod_four hc hz.1
  have hmod := congrArg (fun n : Nat => n % 4) heq
  change (a ^ 4 + b ^ y) % 4 = c ^ z % 4 at hmod
  rw [Nat.add_mod, ha4, hc4] at hmod
  have hlt : b ^ y % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize hr : b ^ y % 4 = r at hmod hlt ⊢
  cases r with
  | zero =>
      simp at hmod
  | succ r =>
      cases r with
      | zero =>
          simp at hmod
      | succ r =>
          cases r with
          | zero =>
              simp at hmod
          | succ r =>
              cases r with
              | zero =>
                  rfl
              | succ r =>
                  have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ r))) := by
                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le r))))
                  exact False.elim ((Nat.not_le_of_gt hlt) hge)

/-- Symmetric residue restriction when the second left exponent is four. -/
theorem T14_c_even_right_four_forces_left_three
    {a b c x y z : Nat}
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hc : T12Even c)
    (hy4 : y = 4) :
    a ^ x % 4 = 3 := by
  have hnb : ¬ T12Even b := by
    rcases hpar with ha | hb | hcOnly
    · exact ha.2.1
    · exact False.elim (hb.2.2 hc)
    · exact hcOnly.2.1
  have hob : T12Odd b := (T12_not_even_iff_odd b).mp hnb
  subst y
  have hb4 : b ^ 4 % 4 = 1 := T13_odd_fourth_mod_four hob
  have hc4 : c ^ z % 4 = 0 := T13_even_pow_mod_four hc hz.1
  have hmod := congrArg (fun n : Nat => n % 4) heq
  change (a ^ x + b ^ 4) % 4 = c ^ z % 4 at hmod
  rw [Nat.add_mod, hb4, hc4] at hmod
  have hlt : a ^ x % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize hr : a ^ x % 4 = r at hmod hlt ⊢
  cases r with
  | zero =>
      simp at hmod
  | succ r =>
      cases r with
      | zero =>
          simp at hmod
      | succ r =>
          cases r with
          | zero =>
              simp at hmod
          | succ r =>
              cases r with
              | zero =>
                  rfl
              | succ r =>
                  have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ r))) := by
                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le r))))
                  exact False.elim ((Nat.not_le_of_gt hlt) hge)

def T14CResidueConstraint (a b c x y z : Nat) : Prop :=
  T12Even c →
    (x = 4 → b ^ y % 4 = 3) ∧
    (y = 4 → a ^ x % 4 = 3)

/-- T14 preserves the full T13 residual and adds explicit modulo-4 data for
    both surviving mixed-four branches when C is the unique even base. -/
def T14ResidueReducedCandidate : Prop :=
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
    T14CResidueConstraint a b c x y z

theorem T14_T13_to_residue :
    T13ModularReducedCandidate → T14ResidueReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hcpos, hx, hy, hz, heq, hpw, hpar, h44, ?_⟩
  intro hce
  constructor
  · intro hx4
    exact T14_c_even_left_four_forces_right_three hz heq hpar hce hx4
  · intro hy4
    exact T14_c_even_right_four_forces_left_three hz heq hpar hce hy4

theorem T14_residue_to_T13 :
    T14ResidueReducedCandidate → T13ModularReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar, h44⟩

theorem T14_candidate_iff_residue :
    T13ModularReducedCandidate ↔ T14ResidueReducedCandidate :=
  ⟨T14_T13_to_residue, T14_residue_to_T13⟩

def T14ResidueScientificFrontier : Prop :=
  ¬ T14ResidueReducedCandidate

theorem T14_beal_iff_residue_frontier :
    BealConjecture ↔ T14ResidueScientificFrontier := by
  rw [T13_beal_iff_modular_frontier]
  unfold T13ModularScientificFrontier T14ResidueScientificFrontier
  exact not_congr T14_candidate_iff_residue

#print axioms MCore.T14_c_even_left_four_forces_right_three
#print axioms MCore.T14_c_even_right_four_forces_left_three
#print axioms MCore.T14_candidate_iff_residue
#print axioms MCore.T14_beal_iff_residue_frontier

end MCore
