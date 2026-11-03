import MCore.BealSpecification

namespace MCore.Beal

/-
T7-BEAL-REJECTION

Purpose:
* keep the genuine Beal equation separate from symmetry / normalization data;
* use an involution for swapping (a,x) <-> (b,y);
* do not pretend that gcd-factorization preserves a mixed-exponent Beal equation;
* expose, rather than assume, the primitive-exclusion endpoint.

This file intentionally proves only structural facts and a negative model.
It contains no proof of BealConjecture.
-/

/-- Material observable on an actual Beal solution. -/
def observedDefect (d : MCore.BealData) : Nat :=
  Nat.gcd (Nat.gcd d.a d.b) d.c

/-- Q1: swap the complete base/exponent pairs, not only the bases. -/
def swapAB (d : MCore.BealData) : MCore.BealData where
  a := d.b
  b := d.a
  c := d.c
  x := d.y
  y := d.x
  z := d.z
  a_pos := d.b_pos
  b_pos := d.a_pos
  c_pos := d.c_pos
  x_gt_two := d.y_gt_two
  y_gt_two := d.x_gt_two
  z_gt_two := d.z_gt_two
  equation := by
    simpa [Nat.add_comm] using d.equation

/-- Q2: the swap is an involution. -/
@[simp] theorem swapAB_involutive (d : MCore.BealData) :
    swapAB (swapAB d) = d := by
  cases d
  rfl

/-- Q3: the gcd observable is invariant under the swap. -/
theorem observedDefect_swap (d : MCore.BealData) :
    observedDefect (swapAB d) = observedDefect d := by
  simp [observedDefect, swapAB, Nat.gcd_comm]

/--
Q4: gcd normalization belongs to the space of base triples, not to the
space of mixed-exponent Beal solutions.  Dividing a,b,c by a common d does
not in general preserve a^x + b^y = c^z when x,y,z are different.
-/
structure BealBaseTriple where
  a : Nat
  b : Nat
  c : Nat

def baseGCD (t : BealBaseTriple) : Nat :=
  Nat.gcd (Nat.gcd t.a t.b) t.c

/--
Abstract normalization interface.

Q5 is the *correct* idempotence law to demand of a normalization map.
It is deliberately not instantiated here by a bogus
BealData -> BealData gcd-division map.
-/
structure FactorNormalization where
  factor : BealBaseTriple -> BealBaseTriple
  factor_idempotent : ∀ t, factor (factor t) = factor t

/--
The structural rejection package.  These are precisely the kinds of laws
that can be inherited from an orbit/invariance argument without injecting
the Beal endpoint.
-/
structure BealRejectionModel where
  Point : Type
  swap : Point -> Point
  factor : Point -> Point
  defect : Point -> Nat
  swap_involutive : ∀ x, swap (swap x) = x
  factor_idempotent : ∀ x, factor (factor x) = factor x
  defect_swap : ∀ x, defect (swap x) = defect x

/-- Q6/Q7/Q8: all structural laws admit a completely coprime orbit. -/
def toyCoprime : BealRejectionModel where
  Point := Unit
  swap := id
  factor := id
  defect := fun _ => 1
  swap_involutive := by intro x; rfl
  factor_idempotent := by intro x; rfl
  defect_swap := by intro x; rfl

theorem toyCoprime_has_defect_one :
    ∃ x : toyCoprime.Point, toyCoprime.defect x = 1 := by
  exact ⟨(), rfl⟩

/--
Q9 / FORBIDDEN_PROMOTION.

The involution + factor-idempotence + defect-invariance schema is
consistent with defect = 1.  Therefore those structural laws alone cannot
serve as a derivation of the Beal endpoint.
-/
theorem structural_schema_allows_defect_one :
    ∃ (M : BealRejectionModel) (x : M.Point), M.defect x = 1 := by
  exact ⟨toyCoprime, (), rfl⟩

/--
Q10 / MATERIAL_PRIMITIVE_EXCLUSION.

This is the actual open-math endpoint in gcd language.  It is a proposition
only; this file does NOT manufacture an inhabitant of it.
-/
def MaterialPrimitiveExclusion : Prop :=
  ∀ d : MCore.BealData, observedDefect d = 1 -> False

/--
A useful exact target: a producer of MaterialPrimitiveExclusion eliminates
every gcd-one actual Beal solution.
-/
theorem materialPrimitiveExclusion_eliminates
    (h : MaterialPrimitiveExclusion)
    (d : MCore.BealData)
    (hd : observedDefect d = 1) :
    False :=
  h d hd

/--
The swap orbit preserves primitiveness exactly; it cannot create the
required common factor.
-/
theorem primitive_swap_iff (d : MCore.BealData) :
    observedDefect (swapAB d) = 1 ↔ observedDefect d = 1 := by
  rw [observedDefect_swap]

end MCore.Beal
