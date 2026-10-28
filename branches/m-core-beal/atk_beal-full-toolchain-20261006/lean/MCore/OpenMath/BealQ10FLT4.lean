import MCore.OpenMath.BealQ10PrimitiveExclusion
import Mathlib.NumberTheory.FLT.Four

namespace MCore.OpenMath.BealQ10

/-- Mathlib-backed elimination of the all-four Beal signature. -/
theorem primitive_allFour_impossible
    (d : MCore.BealData)
    (_hd : PrimitiveBealSolution d)
    (hx : d.x = 4)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    False := by
  have hne :
      d.a ^ 4 + d.b ^ 4 ≠ d.c ^ 4 :=
    fermatLastTheoremFour
      d.a d.b d.c
      (Nat.ne_of_gt d.a_pos)
      (Nat.ne_of_gt d.b_pos)
      (Nat.ne_of_gt d.c_pos)
  apply hne
  simpa [hx, hy, hz] using d.equation

#print axioms MCore.OpenMath.BealQ10.primitive_allFour_impossible

end MCore.OpenMath.BealQ10
