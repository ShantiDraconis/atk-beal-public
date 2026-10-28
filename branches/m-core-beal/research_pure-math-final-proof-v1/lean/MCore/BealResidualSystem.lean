import MCore.K10

namespace MCore

/-- A counterexample candidate in the exact endpoint sense. -/
structure PrimitiveBealCandidate where
  data : BealData
  noCommonPrime : BealCounterexample data

/-- The first exact reduction is lossless: it merely packages the witness. -/
theorem noCommonPrimeCandidate_iff_primitive :
    NoCommonPrimeCandidate ↔ Nonempty PrimitiveBealCandidate := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨⟨d, hd⟩⟩
  · rintro ⟨d⟩
    exact ⟨d.data, d.noCommonPrime⟩

/-- Arithmetic normal form carried by every primitive candidate. -/
structure NormalizedBealCandidate extends PrimitiveBealCandidate where
  exponentBounds : 3 ≤ data.x ∧ 3 ≤ data.y ∧ 3 ≤ data.z
  equationExact : data.a ^ data.x + data.b ^ data.y = data.c ^ data.z

def normalizePrimitive (d : PrimitiveBealCandidate) : NormalizedBealCandidate :=
  { d with
    exponentBounds := ⟨d.data.x_gt_two, d.data.y_gt_two, d.data.z_gt_two⟩
    equationExact := d.data.equation }

theorem primitive_iff_normalized :
    Nonempty PrimitiveBealCandidate ↔ Nonempty NormalizedBealCandidate := by
  constructor
  · rintro ⟨d⟩
    exact ⟨normalizePrimitive d⟩
  · rintro ⟨d⟩
    exact ⟨d.toPrimitiveBealCandidate⟩

/-- Exact mathematical residual after all currently proved reductions. -/
def PrimitiveObstruction : Prop :=
  ¬ Nonempty NormalizedBealCandidate

theorem primitiveObstruction_iff_beal :
    PrimitiveObstruction ↔ BealConjecture := by
  rw [← not_congr primitive_iff_normalized]
  unfold PrimitiveObstruction
  rw [noCommonPrimeCandidate_iff_primitive, noCommonPrimeCandidate_iff_not_beal]
  apply Classical.not_not

/-- Status carrier for the M-Core-style arbiter. No constructor promotes an open residual. -/
inductive ResidualStatus
  | proved
  | refuted
  | blocking
  | openExact
  deriving DecidableEq, Repr

structure BealResidualNode where
  id : String
  statement : Prop
  status : ResidualStatus

def bealPrimitiveNode : BealResidualNode :=
  { id := "BEAL-PRIMITIVE-OBSTRUCTION"
    statement := PrimitiveObstruction
    status := .openExact }

end MCore
