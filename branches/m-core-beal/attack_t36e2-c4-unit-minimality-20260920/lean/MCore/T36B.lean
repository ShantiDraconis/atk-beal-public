import MCore.T36A
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic.Ring

namespace MCore

open WeierstrassCurve

/-- The Frey Weierstrass model over Q attached to
    A = a^x, B = b^y:
      Y^2 = X (X - A) (X + B)
          = X^3 + (B-A)X^2 - ABX.
    This is the actual Mathlib Weierstrass object used by later reduction
    theory; no semantic reduction claim is made here. -/
def T36BFreyCurveQ (a b x y : Nat) : WeierstrassCurve ℚ :=
  let A : ℚ := ((a ^ x : Nat) : ℚ)
  let B : ℚ := ((b ^ y : Nat) : ℚ)
  ⟨0, B - A, 0, -(A * B), 0⟩

/-- Symbolic c4 identity for the actual Mathlib Frey model. -/
theorem T36B_frey_c4_formula (a b x y : Nat) :
    (T36BFreyCurveQ a b x y).c₄ =
      16 * ((((a ^ x : Nat) : ℚ) ^ 2) +
        ((a ^ x : Nat) : ℚ) * ((b ^ y : Nat) : ℚ) +
        (((b ^ y : Nat) : ℚ) ^ 2)) := by
  unfold T36BFreyCurveQ WeierstrassCurve.c₄
    WeierstrassCurve.b₂ WeierstrassCurve.b₄
  ring

/-- Symbolic discriminant identity for the actual Mathlib Frey model. -/
theorem T36B_frey_delta_formula (a b x y : Nat) :
    (T36BFreyCurveQ a b x y).Δ =
      16 * (((a ^ x : Nat) : ℚ) ^ 2) *
        (((b ^ y : Nat) : ℚ) ^ 2) *
        ((((a ^ x : Nat) : ℚ) + ((b ^ y : Nat) : ℚ)) ^ 2) := by
  unfold T36BFreyCurveQ WeierstrassCurve.Δ
    WeierstrassCurve.b₂ WeierstrassCurve.b₄
    WeierstrassCurve.b₆ WeierstrassCurve.b₈
  ring

/-- T32's natural-number c4 kernel is exactly the c4 of the Mathlib Frey
    curve after coercion to Q. -/
theorem T36B_frey_c4_eq_nat_kernel (a b x y : Nat) :
    (T36BFreyCurveQ a b x y).c₄ =
      ((T32FreyC4Kernel a b x y : Nat) : ℚ) := by
  rw [T36B_frey_c4_formula]
  unfold T32FreyC4Kernel
  norm_num

/-- The algebraic discriminant formula is exactly T24's natural-number
    Frey discriminant kernel after coercion to Q. -/
theorem T36B_frey_delta_eq_nat_kernel (a b x y : Nat) :
    (T36BFreyCurveQ a b x y).Δ =
      ((T24FreyDiscriminantKernel a b x y : Nat) : ℚ) := by
  rw [T36B_frey_delta_formula]
  unfold T24FreyDiscriminantKernel
  norm_num

/-- Under the Beal equation, T24's Beal normal form follows by the already
    proved exact natural-number rewrite, rather than rewriting inside casts. -/
theorem T36B_frey_delta_eq_nat_beal
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    (T36BFreyCurveQ a b x y).Δ =
      ((T24FreyDiscriminantBeal a b c x y z : Nat) : ℚ) := by
  calc
    (T36BFreyCurveQ a b x y).Δ =
        ((T24FreyDiscriminantKernel a b x y : Nat) : ℚ) :=
      T36B_frey_delta_eq_nat_kernel a b x y
    _ = ((T24FreyDiscriminantBeal a b c x y z : Nat) : ℚ) := by
      exact_mod_cast T24_frey_discriminant_rewrite heq

/-- The exact adapter package needed before moving from elementary Nat
    divisibility to local valuations. -/
structure T36BFreyInvariantAdapter
    (a b c x y z : Nat) : Prop where
  equation : a ^ x + b ^ y = c ^ z
  c4_exact :
    (T36BFreyCurveQ a b x y).c₄ =
      ((T32FreyC4Kernel a b x y : Nat) : ℚ)
  delta_exact :
    (T36BFreyCurveQ a b x y).Δ =
      ((T24FreyDiscriminantBeal a b c x y z : Nat) : ℚ)

/-- The invariant adapter is constructed without any new axiom. -/
theorem T36B_build_frey_invariant_adapter
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    T36BFreyInvariantAdapter a b c x y z := by
  exact ⟨heq, T36B_frey_c4_eq_nat_kernel a b x y,
    T36B_frey_delta_eq_nat_beal heq⟩

/-- What remains after T36B is no longer the curve/invariant identification:
    it is specifically the local-valuation adapter at p. -/
def T36BLocalValuationAdapterGoal : Prop :=
  ∀ a b c x y z p : Nat,
    T36OddLocalArithmeticPackage a b c x y z p →
    ∃ (_W : WeierstrassCurve ℚ),
      _W = T36BFreyCurveQ a b x y

#print axioms MCore.T36B_frey_c4_formula
#print axioms MCore.T36B_frey_delta_formula
#print axioms MCore.T36B_frey_c4_eq_nat_kernel
#print axioms MCore.T36B_frey_delta_eq_nat_kernel
#print axioms MCore.T36B_frey_delta_eq_nat_beal
#print axioms MCore.T36B_build_frey_invariant_adapter

end MCore
