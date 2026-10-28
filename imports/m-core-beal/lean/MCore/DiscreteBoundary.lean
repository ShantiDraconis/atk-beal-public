import MCore.BealSpecification

namespace MCore

theorem exponent_three_le (d : BealData) : 3 ≤ d.x ∧ 3 ≤ d.y ∧ 3 ≤ d.z := by
  exact ⟨d.x_gt_two, d.y_gt_two, d.z_gt_two⟩

theorem candidate_equation (d : BealData) : d.a ^ d.x + d.b ^ d.y = d.c ^ d.z :=
  d.equation

/-- The boundary data are carried explicitly; no analytic 0/0 limit is introduced. -/
theorem admissible_boundary_data (d : BealData) :
    0 < d.a ∧ 0 < d.b ∧ 0 < d.c ∧ 2 < d.x ∧ 2 < d.y ∧ 2 < d.z := by
  exact ⟨d.a_pos, d.b_pos, d.c_pos, d.x_gt_two, d.y_gt_two, d.z_gt_two⟩

end MCore
