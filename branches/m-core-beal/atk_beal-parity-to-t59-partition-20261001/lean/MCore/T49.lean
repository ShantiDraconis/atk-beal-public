import MCore.T48

namespace MCore

/-!
T49 — THE "CONTAINS 4" MIXED FAMILY

The T48 contains-four family splits exactly into:
* all three exponents equal 4;
* exactly two exponents equal 4;
* exactly one exponent equal 4.

The all-four branch is literally FLT(4), already formalized in Mathlib.
This module proves the reduction but does not import Mathlib yet.
-/

def T49AllFour (x y z : Nat) : Prop :=
  x = 4 ∧ y = 4 ∧ z = 4

def T49ExactlyTwoFour (x y z : Nat) : Prop :=
  (x = 4 ∧ y = 4 ∧ z ≠ 4) ∨
  (x = 4 ∧ z = 4 ∧ y ≠ 4) ∨
  (y = 4 ∧ z = 4 ∧ x ≠ 4)

def T49ExactlyOneFour (x y z : Nat) : Prop :=
  (x = 4 ∧ y ≠ 4 ∧ z ≠ 4) ∨
  (y = 4 ∧ x ≠ 4 ∧ z ≠ 4) ∨
  (z = 4 ∧ x ≠ 4 ∧ y ≠ 4)

theorem T49_contains_four_trichotomy
    {x y z : Nat}
    (h : T48ContainsFour x y z) :
    T49AllFour x y z ∨
      T49ExactlyTwoFour x y z ∨
      T49ExactlyOneFour x y z := by
  by_cases hx : x = 4
  · by_cases hy : y = 4
    · by_cases hz : z = 4
      · exact Or.inl ⟨hx, hy, hz⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hx, hy, hz⟩))
    · by_cases hz : z = 4
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hx, hz, hy⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨hx, hy, hz⟩))
  · by_cases hy : y = 4
    · by_cases hz : z = 4
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hy, hz, hx⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hy, hx, hz⟩)))
    · have hz : z = 4 := by
        rcases h with hx4 | hy4 | hz4
        · exact False.elim (hx hx4)
        · exact False.elim (hy hy4)
        · exact hz4
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hz, hx, hy⟩)))

theorem T49_all_four_beal_equation_is_flt4
    {a b c x y z : Nat}
    (h4 : T49AllFour x y z)
    (heq : a ^ x + b ^ y = c ^ z) :
    a ^ 4 + b ^ 4 = c ^ 4 := by
  rcases h4 with ⟨rfl, rfl, rfl⟩
  exact heq

/-- Local FLT contract, kept branch-independent from sibling T47. -/
def T49FLTAt (n : Nat) : Prop :=
  ∀ a b c : Nat,
    0 < a →
    0 < b →
    0 < c →
    a ^ n + b ^ n = c ^ n →
    False

/-- A certified FLT(4) theorem eliminates the all-four Beal branch. -/
theorem T49_flt4_eliminates_all_four
    {a b c x y z : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h4 : T49AllFour x y z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hFLT4 : T49FLTAt 4) :
    False := by
  exact hFLT4 a b c ha hb hc
    (T49_all_four_beal_equation_is_flt4 h4 heq)

/-- After FLT(4) is supplied, only the one-four and two-four mixed
    signatures remain inside T48's contains-four family. -/
def T49ContainsFourResidual (x y z : Nat) : Prop :=
  T49ExactlyTwoFour x y z ∨ T49ExactlyOneFour x y z

theorem T49_contains_four_reduced_by_flt4
    {x y z : Nat}
    (hContains : T48ContainsFour x y z)
    (hNotAllFour : ¬ T49AllFour x y z) :
    T49ContainsFourResidual x y z := by
  rcases T49_contains_four_trichotomy hContains with hAll | hTwo | hOne
  · exact False.elim (hNotAllFour hAll)
  · exact Or.inl hTwo
  · exact Or.inr hOne

#print axioms MCore.T49_contains_four_trichotomy
#print axioms MCore.T49_all_four_beal_equation_is_flt4
#print axioms MCore.T49_flt4_eliminates_all_four
#print axioms MCore.T49_contains_four_reduced_by_flt4

end MCore
