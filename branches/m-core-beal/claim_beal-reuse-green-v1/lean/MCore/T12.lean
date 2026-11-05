import Init.Data.Nat.Lemmas
import MCore.T11

namespace MCore

def T12Even (n : Nat) : Prop :=
  2 ∣ n

def T12Odd (n : Nat) : Prop :=
  n % 2 = 1

def T12EvenDecidable (n : Nat) : Decidable (T12Even n) := by
  unfold T12Even
  exact Nat.decidable_dvd 2 n

theorem T12_not_even_iff_odd (n : Nat) :
    (¬ T12Even n) ↔ T12Odd n := by
  unfold T12Even T12Odd
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    have hle : n % 2 ≤ 1 := Nat.le_of_lt_succ hlt
    have hge : 1 ≤ n % 2 := Nat.succ_le_of_lt hpos
    exact Nat.le_antisymm hle hge
  · intro hodd hdvd
    have hzero : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    rw [hodd] at hzero
    exact Nat.one_ne_zero hzero

theorem T12_odd_pow_mod_two
    {a n : Nat} (ha : T12Odd a) :
    a ^ n % 2 = 1 := by
  unfold T12Odd at ha
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, ha]

theorem T12_some_base_even
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    T12Even a ∨ T12Even b ∨ T12Even c := by
  match T12EvenDecidable a with
  | isTrue ha =>
      exact Or.inl ha
  | isFalse ha =>
      match T12EvenDecidable b with
      | isTrue hb =>
          exact Or.inr (Or.inl hb)
      | isFalse hb =>
          match T12EvenDecidable c with
          | isTrue hc =>
              exact Or.inr (Or.inr hc)
          | isFalse hc =>
              have hoa : T12Odd a := (T12_not_even_iff_odd a).mp ha
              have hob : T12Odd b := (T12_not_even_iff_odd b).mp hb
              have hoc : T12Odd c := (T12_not_even_iff_odd c).mp hc
              have hax : a ^ x % 2 = 1 := T12_odd_pow_mod_two hoa
              have hby : b ^ y % 2 = 1 := T12_odd_pow_mod_two hob
              have hcz : c ^ z % 2 = 1 := T12_odd_pow_mod_two hoc
              have hmod := congrArg (fun n : Nat => n % 2) heq
              have hleft : (a ^ x + b ^ y) % 2 = 0 := by
                rw [Nat.add_mod, hax, hby]
              change (a ^ x + b ^ y) % 2 = c ^ z % 2 at hmod
              rw [hleft, hcz] at hmod
              exact False.elim (Nat.zero_ne_one hmod)

def T12ExactlyOneEven (a b c : Nat) : Prop :=
  (T12Even a ∧ ¬ T12Even b ∧ ¬ T12Even c) ∨
  (¬ T12Even a ∧ T12Even b ∧ ¬ T12Even c) ∨
  (¬ T12Even a ∧ ¬ T12Even b ∧ T12Even c)

theorem T12_exactly_one_even_of_pairwise
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c) :
    T12ExactlyOneEven a b c := by
  have hab : ¬ (T12Even a ∧ T12Even b) := by
    rintro ⟨ha, hb⟩
    apply hpw.1
    exact ⟨2, by decide, ha, hb⟩
  have hac : ¬ (T12Even a ∧ T12Even c) := by
    rintro ⟨ha, hc⟩
    apply hpw.2.1
    exact ⟨2, by decide, ha, hc⟩
  have hbc : ¬ (T12Even b ∧ T12Even c) := by
    rintro ⟨hb, hc⟩
    apply hpw.2.2
    exact ⟨2, by decide, hb, hc⟩
  rcases T12_some_base_even heq with ha | hb | hc
  · left
    refine ⟨ha, ?_, ?_⟩
    · intro hb
      exact hab ⟨ha, hb⟩
    · intro hc
      exact hac ⟨ha, hc⟩
  · right
    left
    refine ⟨?_, hb, ?_⟩
    · intro ha
      exact hab ⟨ha, hb⟩
    · intro hc
      exact hbc ⟨hb, hc⟩
  · right
    right
    refine ⟨?_, ?_, hc⟩
    · intro ha
      exact hac ⟨ha, hc⟩
    · intro hb
      exact hbc ⟨hb, hc⟩

/-- T12 keeps the T11 reduced signature and exposes the forced parity state. -/
def T12ParityReducedCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c ∧
    T12ExactlyOneEven a b c

theorem T12_T11_to_parity :
    T11PairwiseReducedCandidate → T12ParityReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw,
    T12_exactly_one_even_of_pairwise heq hpw⟩

theorem T12_parity_to_T11 :
    T12ParityReducedCandidate → T11PairwiseReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw⟩

theorem T12_candidate_iff_parity :
    T11PairwiseReducedCandidate ↔ T12ParityReducedCandidate :=
  ⟨T12_T11_to_parity, T12_parity_to_T11⟩

def T12ParityScientificFrontier : Prop :=
  ¬ T12ParityReducedCandidate

theorem T12_beal_iff_parity_frontier :
    BealConjecture ↔ T12ParityScientificFrontier := by
  rw [T11_beal_iff_pairwise_frontier]
  unfold T11PairwiseScientificFrontier T12ParityScientificFrontier
  exact not_congr T12_candidate_iff_parity

#print axioms MCore.T12_not_even_iff_odd
#print axioms MCore.T12_odd_pow_mod_two
#print axioms MCore.T12_some_base_even
#print axioms MCore.T12_exactly_one_even_of_pairwise
#print axioms MCore.T12_candidate_iff_parity
#print axioms MCore.T12_beal_iff_parity_frontier

end MCore
