import MCore.T60
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

namespace MCore

/-!
T61 — ACTUAL GENERALIZED FREY WEIERSTRASS MODEL

For u = A^x and v = B^y, use
  Y^2 = X (X - u) (X + v)
      = X^3 + (v-u) X^2 - uv X.

This module constructs the actual Weierstrass curve over Z and Q and proves
the exact c4 and discriminant identities in Mathlib.
-/

open WeierstrassCurve

/-- Integral generalized Frey model. -/
def T61FreyCurveZ (a b x y : Nat) : WeierstrassCurve ℤ :=
  ⟨
    0,
    ((b ^ y : Nat) : ℤ) - ((a ^ x : Nat) : ℤ),
    0,
    -(((a ^ x : Nat) : ℤ) * ((b ^ y : Nat) : ℤ)),
    0
  ⟩

/-- Rational base-change of the integral generalized Frey model. -/
def T61FreyCurveQ (a b x y : Nat) : WeierstrassCurve ℚ :=
  (T61FreyCurveZ a b x y).baseChange ℚ

/-- Exact c4 invariant of the generalized Frey model. -/
theorem T61_freyCurveZ_c4
    (a b x y : Nat) :
    (T61FreyCurveZ a b x y).c₄ =
      16 * (
        (((a ^ x : Nat) : ℤ) ^ 2) +
        (((a ^ x : Nat) : ℤ) * ((b ^ y : Nat) : ℤ)) +
        (((b ^ y : Nat) : ℤ) ^ 2)
      ) := by
  simp only [
    T61FreyCurveZ,
    WeierstrassCurve.c₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄
  ]
  ring

/-- Exact discriminant of the generalized Frey model. -/
theorem T61_freyCurveZ_delta
    (a b x y : Nat) :
    (T61FreyCurveZ a b x y).Δ =
      16 *
      (((a ^ x : Nat) : ℤ) ^ 2) *
      (((b ^ y : Nat) : ℤ) ^ 2) *
      ((((a ^ x : Nat) : ℤ) + ((b ^ y : Nat) : ℤ)) ^ 2) := by
  simp only [
    T61FreyCurveZ,
    WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,
    WeierstrassCurve.b₈
  ]
  ring

/-- The rational c4 is the coercion of the integral invariant. -/
theorem T61_freyCurveQ_c4
    (a b x y : Nat) :
    (T61FreyCurveQ a b x y).c₄ =
      algebraMap ℤ ℚ (T61FreyCurveZ a b x y).c₄ := by
  simp [T61FreyCurveQ]

/-- The rational discriminant is the coercion of the integral invariant. -/
theorem T61_freyCurveQ_delta
    (a b x y : Nat) :
    (T61FreyCurveQ a b x y).Δ =
      algebraMap ℤ ℚ (T61FreyCurveZ a b x y).Δ := by
  simp [T61FreyCurveQ]

/-- Exact bridge from the old natural-number c4 kernel to the actual integral
    Weierstrass c4. -/
theorem T61_c4_matches_T32_kernel
    (a b x y : Nat) :
    (T61FreyCurveZ a b x y).c₄ =
      (T32FreyC4Kernel a b x y : ℤ) := by
  rw [T61_freyCurveZ_c4]
  unfold T32FreyC4Kernel
  norm_num
  push_cast
  ring

/-- Exact bridge from the old natural-number raw discriminant kernel to the
    actual integral Weierstrass discriminant, using the Beal equation. -/
theorem T61_delta_matches_T24_kernel
    (d : T59ResidualCandidate) :
    (T61FreyCurveZ d.a d.b d.x d.y).Δ =
      (T24FreyDiscriminantBeal
        d.a d.b d.c d.x d.y d.z : ℤ) := by
  rw [T61_freyCurveZ_delta]
  unfold T24FreyDiscriminantBeal
  have heqZ :
      (((d.a ^ d.x : Nat) : ℤ) + ((d.b ^ d.y : Nat) : ℤ)) =
        ((d.c ^ d.z : Nat) : ℤ) := by
    exact_mod_cast d.equation
  rw [heqZ]
  norm_num
  push_cast
  ring

#print axioms MCore.T61_freyCurveZ_c4
#print axioms MCore.T61_freyCurveZ_delta
#print axioms MCore.T61_freyCurveQ_c4
#print axioms MCore.T61_freyCurveQ_delta
#print axioms MCore.T61_c4_matches_T32_kernel
#print axioms MCore.T61_delta_matches_T24_kernel

end MCore
