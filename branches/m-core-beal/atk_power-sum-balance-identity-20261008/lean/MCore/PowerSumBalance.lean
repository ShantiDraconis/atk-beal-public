import MCore.GCDLowerBoundProducer

namespace MCore

/-- Kernel-visible balance identity extracted directly from the power-sum
equation.  This is the division-free form of the X/Y contraction:
X = a^x and Y = b^y - c^z, hence X + Y = 0. -/
theorem powerSum_balance_int (d : BealData) :
    (d.a ^ d.x : Int) +
        ((d.b ^ d.y : Int) - (d.c ^ d.z : Int)) = 0 := by
  have h :
      (d.a ^ d.x : Int) + (d.b ^ d.y : Int) =
        (d.c ^ d.z : Int) := by
    exact_mod_cast d.equation
  omega

/-- Equivalent signed form of the same material identity. -/
theorem powerSum_signed_ratio_numerator_int (d : BealData) :
    (d.b ^ d.y : Int) - (d.c ^ d.z : Int) =
      -(d.a ^ d.x : Int) := by
  have h := powerSum_balance_int d
  omega

/-- The chosen denominator X=a^x is nonzero on the positive domain. -/
theorem powerSum_X_ne_zero_int (d : BealData) :
    (d.a ^ d.x : Int) ≠ 0 := by
  have ha : (d.a : Int) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt d.a_pos)
  exact pow_ne_zero _ ha

#print axioms MCore.powerSum_balance_int
#print axioms MCore.powerSum_signed_ratio_numerator_int
#print axioms MCore.powerSum_X_ne_zero_int

end MCore
