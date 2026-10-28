import MCore.T17

namespace MCore

theorem T18_a_even_other_odd
    {a b c : Nat}
    (hpar : T12ExactlyOneEven a b c)
    (ha : T12Even a) :
    T12Odd b ∧ T12Odd c := by
  have hnb : ¬ T12Even b := by
    rcases hpar with haOnly | hbOnly | hcOnly
    · exact haOnly.2.1
    · exact False.elim (hbOnly.1 ha)
    · exact hcOnly.2.1
  have hnc : ¬ T12Even c := by
    rcases hpar with haOnly | hbOnly | hcOnly
    · exact haOnly.2.2
    · exact hbOnly.2.2
    · exact False.elim (hcOnly.1 ha)
  exact ⟨(T12_not_even_iff_odd b).mp hnb, (T12_not_even_iff_odd c).mp hnc⟩

theorem T18_b_even_other_odd
    {a b c : Nat}
    (hpar : T12ExactlyOneEven a b c)
    (hb : T12Even b) :
    T12Odd a ∧ T12Odd c := by
  have hna : ¬ T12Even a := by
    rcases hpar with haOnly | hbOnly | hcOnly
    · exact False.elim (haOnly.2.1 hb)
    · exact hbOnly.1
    · exact hcOnly.1
  have hnc : ¬ T12Even c := by
    rcases hpar with haOnly | hbOnly | hcOnly
    · exact haOnly.2.2
    · exact hbOnly.2.2
    · exact False.elim (hcOnly.2.1 hb)
  exact ⟨(T12_not_even_iff_odd a).mp hna, (T12_not_even_iff_odd c).mp hnc⟩

theorem T18_a_even_power_residue_eq
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (heq : a ^ x + b ^ y = c ^ z)
    (ha : T12Even a) :
    b ^ y % 8 = c ^ z % 8 := by
  have ha8 : a ^ x % 8 = 0 := T16_even_pow_mod_eight ha hx.1
  have hmod := congrArg (fun n : Nat => n % 8) heq
  change (a ^ x + b ^ y) % 8 = c ^ z % 8 at hmod
  rw [Nat.add_mod, ha8] at hmod
  simpa using hmod

theorem T18_b_even_power_residue_eq
    {a b c x y z : Nat}
    (hy : T7ReducedExponent y)
    (heq : a ^ x + b ^ y = c ^ z)
    (hb : T12Even b) :
    a ^ x % 8 = c ^ z % 8 := by
  have hb8 : b ^ y % 8 = 0 := T16_even_pow_mod_eight hb hy.1
  have hmod := congrArg (fun n : Nat => n % 8) heq
  change (a ^ x + b ^ y) % 8 = c ^ z % 8 at hmod
  rw [Nat.add_mod, hb8] at hmod
  simpa using hmod

theorem T18_a_even_y_four_z_odd
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (ha : T12Even a)
    (hy4 : y = 4)
    (hzne4 : z ≠ 4) :
    c % 8 = 1 := by
  rcases T18_a_even_other_odd hpar ha with ⟨hob, hoc⟩
  have hres : b ^ y % 8 = c ^ z % 8 :=
    T18_a_even_power_residue_eq hx heq ha
  have hb4 : b ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hob
  have hoz : T12Odd z := T17_reduced_ne_four_odd hz hzne4
  have hcz : c ^ z % 8 = c % 8 := T17_odd_pow_mod_eight_eq_base hoc hoz
  calc
    c % 8 = c ^ z % 8 := hcz.symm
    _ = b ^ y % 8 := hres.symm
    _ = 1 := by rw [hy4]; exact hb4

theorem T18_a_even_y_odd_z_four
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (ha : T12Even a)
    (hyne4 : y ≠ 4)
    (hz4 : z = 4) :
    b % 8 = 1 := by
  rcases T18_a_even_other_odd hpar ha with ⟨hob, hoc⟩
  have hres : b ^ y % 8 = c ^ z % 8 :=
    T18_a_even_power_residue_eq hx heq ha
  have hoy : T12Odd y := T17_reduced_ne_four_odd hy hyne4
  have hby : b ^ y % 8 = b % 8 := T17_odd_pow_mod_eight_eq_base hob hoy
  have hc4 : c ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hoc
  calc
    b % 8 = b ^ y % 8 := hby.symm
    _ = c ^ z % 8 := hres
    _ = 1 := by rw [hz4]; exact hc4

theorem T18_a_even_odd_odd_residues_eq
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (ha : T12Even a)
    (hyne4 : y ≠ 4)
    (hzne4 : z ≠ 4) :
    b % 8 = c % 8 := by
  rcases T18_a_even_other_odd hpar ha with ⟨hob, hoc⟩
  have hres : b ^ y % 8 = c ^ z % 8 :=
    T18_a_even_power_residue_eq hx heq ha
  have hoy : T12Odd y := T17_reduced_ne_four_odd hy hyne4
  have hoz : T12Odd z := T17_reduced_ne_four_odd hz hzne4
  have hby : b ^ y % 8 = b % 8 := T17_odd_pow_mod_eight_eq_base hob hoy
  have hcz : c ^ z % 8 = c % 8 := T17_odd_pow_mod_eight_eq_base hoc hoz
  calc
    b % 8 = b ^ y % 8 := hby.symm
    _ = c ^ z % 8 := hres
    _ = c % 8 := hcz

theorem T18_b_even_x_four_z_odd
    {a b c x y z : Nat}
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hb : T12Even b)
    (hx4 : x = 4)
    (hzne4 : z ≠ 4) :
    c % 8 = 1 := by
  rcases T18_b_even_other_odd hpar hb with ⟨hoa, hoc⟩
  have hres : a ^ x % 8 = c ^ z % 8 :=
    T18_b_even_power_residue_eq hy heq hb
  have ha4 : a ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hoa
  have hoz : T12Odd z := T17_reduced_ne_four_odd hz hzne4
  have hcz : c ^ z % 8 = c % 8 := T17_odd_pow_mod_eight_eq_base hoc hoz
  calc
    c % 8 = c ^ z % 8 := hcz.symm
    _ = a ^ x % 8 := hres.symm
    _ = 1 := by rw [hx4]; exact ha4

theorem T18_b_even_x_odd_z_four
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hb : T12Even b)
    (hxne4 : x ≠ 4)
    (hz4 : z = 4) :
    a % 8 = 1 := by
  rcases T18_b_even_other_odd hpar hb with ⟨hoa, hoc⟩
  have hres : a ^ x % 8 = c ^ z % 8 :=
    T18_b_even_power_residue_eq hy heq hb
  have hox : T12Odd x := T17_reduced_ne_four_odd hx hxne4
  have hax : a ^ x % 8 = a % 8 := T17_odd_pow_mod_eight_eq_base hoa hox
  have hc4 : c ^ 4 % 8 = 1 := T16_odd_fourth_mod_eight hoc
  calc
    a % 8 = a ^ x % 8 := hax.symm
    _ = c ^ z % 8 := hres
    _ = 1 := by rw [hz4]; exact hc4

theorem T18_b_even_odd_odd_residues_eq
    {a b c x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpar : T12ExactlyOneEven a b c)
    (hb : T12Even b)
    (hxne4 : x ≠ 4)
    (hzne4 : z ≠ 4) :
    a % 8 = c % 8 := by
  rcases T18_b_even_other_odd hpar hb with ⟨hoa, hoc⟩
  have hres : a ^ x % 8 = c ^ z % 8 :=
    T18_b_even_power_residue_eq hy heq hb
  have hox : T12Odd x := T17_reduced_ne_four_odd hx hxne4
  have hoz : T12Odd z := T17_reduced_ne_four_odd hz hzne4
  have hax : a ^ x % 8 = a % 8 := T17_odd_pow_mod_eight_eq_base hoa hox
  have hcz : c ^ z % 8 = c % 8 := T17_odd_pow_mod_eight_eq_base hoc hoz
  calc
    a % 8 = a ^ x % 8 := hax.symm
    _ = c ^ z % 8 := hres
    _ = c % 8 := hcz

def T18AEvenClassifier (a b c x y z : Nat) : Prop :=
  T12Even a →
    (y = 4 → z ≠ 4 → c % 8 = 1) ∧
    (y ≠ 4 → z = 4 → b % 8 = 1) ∧
    (y ≠ 4 → z ≠ 4 → b % 8 = c % 8)

def T18BEvenClassifier (a b c x y z : Nat) : Prop :=
  T12Even b →
    (x = 4 → z ≠ 4 → c % 8 = 1) ∧
    (x ≠ 4 → z = 4 → a % 8 = 1) ∧
    (x ≠ 4 → z ≠ 4 → a % 8 = c % 8)

def T18FullParityClassifiedCandidate : Prop :=
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
    T18BEvenClassifier a b c x y z

theorem T18_T17_to_full :
    T17ClassifiedReducedCandidate → T18FullParityClassifiedCandidate := by
  rintro ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17⟩
  refine ⟨a, b, c, x, y, z, haPos, hbPos, hcPos, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, ?_, ?_⟩
  · intro hae
    constructor
    · intro hy4 hzne4
      exact T18_a_even_y_four_z_odd hx hz heq hpar hae hy4 hzne4
    constructor
    · intro hyne4 hz4
      exact T18_a_even_y_odd_z_four hx hy heq hpar hae hyne4 hz4
    · intro hyne4 hzne4
      exact T18_a_even_odd_odd_residues_eq hx hy hz heq hpar hae hyne4 hzne4
  · intro hbe
    constructor
    · intro hx4 hzne4
      exact T18_b_even_x_four_z_odd hy hz heq hpar hbe hx4 hzne4
    constructor
    · intro hxne4 hz4
      exact T18_b_even_x_odd_z_four hx hy heq hpar hbe hxne4 hz4
    · intro hxne4 hzne4
      exact T18_b_even_odd_odd_residues_eq hx hy hz heq hpar hbe hxne4 hzne4

theorem T18_full_to_T17 :
    T18FullParityClassifiedCandidate → T17ClassifiedReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, _, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17⟩

theorem T18_candidate_iff_full :
    T17ClassifiedReducedCandidate ↔ T18FullParityClassifiedCandidate :=
  ⟨T18_T17_to_full, T18_full_to_T17⟩

def T18FullParityScientificFrontier : Prop :=
  ¬ T18FullParityClassifiedCandidate

theorem T18_beal_iff_full_parity_frontier :
    BealConjecture ↔ T18FullParityScientificFrontier := by
  rw [T17_beal_iff_classified_frontier]
  unfold T17ClassifiedScientificFrontier T18FullParityScientificFrontier
  exact not_congr T18_candidate_iff_full

#print axioms MCore.T18_a_even_power_residue_eq
#print axioms MCore.T18_b_even_power_residue_eq
#print axioms MCore.T18_a_even_odd_odd_residues_eq
#print axioms MCore.T18_b_even_odd_odd_residues_eq
#print axioms MCore.T18_candidate_iff_full
#print axioms MCore.T18_beal_iff_full_parity_frontier

end MCore
