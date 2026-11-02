import MCore.T49
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

namespace MCore

/-!
T50 — CERTIFIED MATHLIB FLT(3)/FLT(4) BRIDGE

This module is intentionally on a lateral branch with Mathlib v4.19.0 pinned.
It converts Mathlib's kernel-checked FLT(3) and FLT(4) theorems into the
internal T49FLTAt contracts used by the Beal signature analysis.
-/

theorem T50_mathlib_flt3 : T49FLTAt 3 := by
  intro a b c ha hb hc heq
  exact (fermatLastTheoremThree
    a b c
    (Nat.ne_of_gt ha)
    (Nat.ne_of_gt hb)
    (Nat.ne_of_gt hc)) heq

theorem T50_mathlib_flt4 : T49FLTAt 4 := by
  intro a b c ha hb hc heq
  exact (fermatLastTheoremFour
    a b c
    (Nat.ne_of_gt ha)
    (Nat.ne_of_gt hb)
    (Nat.ne_of_gt hc)) heq

/-- Equal-prime signature ell=3 is completely eliminated by Mathlib FLT(3). -/
theorem T50_eliminate_equal_three
    {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (heq : a ^ 3 + b ^ 3 = c ^ 3) :
    False :=
  T50_mathlib_flt3 a b c ha hb hc heq

/-- All-four signature is completely eliminated by Mathlib FLT(4). -/
theorem T50_eliminate_all_four
    {a b c x y z : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h4 : T49AllFour x y z)
    (heq : a ^ x + b ^ y = c ^ z) :
    False :=
  T49_flt4_eliminates_all_four ha hb hc h4 heq T50_mathlib_flt4

/-- The two small certified exponent branches currently available directly
    from Mathlib v4.19.0. -/
def T50SmallCertifiedExponent (n : Nat) : Prop :=
  n = 3 ∨ n = 4

theorem T50_small_certified_exponent_has_flt
    {n : Nat}
    (h : T50SmallCertifiedExponent n) :
    T49FLTAt n := by
  rcases h with rfl | rfl
  · exact T50_mathlib_flt3
  · exact T50_mathlib_flt4

#print axioms MCore.T50_mathlib_flt3
#print axioms MCore.T50_mathlib_flt4
#print axioms MCore.T50_eliminate_equal_three
#print axioms MCore.T50_eliminate_all_four
#print axioms MCore.T50_small_certified_exponent_has_flt

end MCore
