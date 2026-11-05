import Mathlib
import MCore.Research.Tristable.Algebra

namespace MCore.Research.Beal

def ternaryD (a b : ℤ) : ℤ := a^2 - a*b + b^2

theorem ternaryD_eq_sum_form (a b : ℤ) :
    ternaryD a b = (a+b)^2 - 3*a*b := by
  unfold ternaryD
  ring

theorem four_mul_ternaryD (a b : ℤ) :
    4 * ternaryD a b = (2*a-b)^2 + 3*b^2 := by
  unfold ternaryD
  ring

theorem ternaryD_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    0 < ternaryD a b := by
  have hs : 0 < (2*a-b)^2 + 3*b^2 := by
    have hb2 : 0 < b^2 := sq_pos_of_pos hb
    nlinarith [sq_nonneg (2*a-b)]
  rw [← four_mul_ternaryD] at hs
  nlinarith

end MCore.Research.Beal
