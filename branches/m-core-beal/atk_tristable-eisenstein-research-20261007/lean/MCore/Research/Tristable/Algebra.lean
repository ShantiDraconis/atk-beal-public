import Mathlib

namespace MCore.Research.Tristable

noncomputable section

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

def defect (a b c : ℂ) : ℂ := a + omega * b + omega^2 * c

def realDefectSq (a b c : ℝ) : ℝ :=
  a^2 + b^2 + c^2 - a*b - b*c - c*a

theorem realDefectSq_eq_pairwise (a b c : ℝ) :
    2 * realDefectSq a b c =
      (a-b)^2 + (b-c)^2 + (c-a)^2 := by
  unfold realDefectSq
  ring

theorem realDefectSq_nonneg (a b c : ℝ) :
    0 ≤ realDefectSq a b c := by
  rw [← mul_nonneg_iff_of_pos_left (show (0:ℝ) < 2 by norm_num)]
  rw [realDefectSq_eq_pairwise]
  positivity

end
end MCore.Research.Tristable
