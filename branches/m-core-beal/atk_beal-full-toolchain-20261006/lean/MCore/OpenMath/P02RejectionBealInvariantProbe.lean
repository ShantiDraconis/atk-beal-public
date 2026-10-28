import MCore.BealSpecification

namespace MCore.OpenMath.BealProbe

def observedDefect (d : MCore.BealData) : Nat :=
  Nat.gcd (Nat.gcd d.a d.b) d.c

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

@[simp] theorem swapAB_involutive (d : MCore.BealData) :
    swapAB (swapAB d) = d := by
  cases d
  rfl

theorem observedDefect_swap (d : MCore.BealData) :
    observedDefect (swapAB d) = observedDefect d := by
  simp [observedDefect, swapAB, Nat.gcd_comm]

structure BealBaseTriple where
  a : Nat
  b : Nat
  c : Nat

def baseGCD (t : BealBaseTriple) : Nat :=
  Nat.gcd (Nat.gcd t.a t.b) t.c

structure FactorNormalization where
  factor : BealBaseTriple -> BealBaseTriple
  factor_idempotent : ∀ t, factor (factor t) = factor t

structure BealRejectionModel where
  Point : Type
  swap : Point -> Point
  factor : Point -> Point
  defect : Point -> Nat
  swap_involutive : ∀ x, swap (swap x) = x
  factor_idempotent : ∀ x, factor (factor x) = factor x
  defect_swap : ∀ x, defect (swap x) = defect x

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

theorem structural_schema_allows_defect_one :
    ∃ (M : BealRejectionModel) (x : M.Point), M.defect x = 1 := by
  exact ⟨toyCoprime, (), rfl⟩

def MaterialPrimitiveExclusion : Prop :=
  ∀ d : MCore.BealData, observedDefect d = 1 -> False

theorem materialPrimitiveExclusion_eliminates
    (h : MaterialPrimitiveExclusion)
    (d : MCore.BealData)
    (hd : observedDefect d = 1) :
    False :=
  h d hd

theorem primitive_swap_iff (d : MCore.BealData) :
    observedDefect (swapAB d) = 1 ↔ observedDefect d = 1 := by
  rw [observedDefect_swap]

end MCore.OpenMath.BealProbe
