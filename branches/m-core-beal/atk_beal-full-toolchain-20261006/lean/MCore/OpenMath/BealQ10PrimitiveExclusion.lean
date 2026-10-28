import MCore.OpenMath.P02RejectionBealInvariantProbe

namespace MCore.OpenMath.BealQ10

open MCore.OpenMath.BealProbe

/-- A primitive actual Beal solution: the exact counterexample shape Q10 must eliminate. -/
def PrimitiveBealSolution (d : MCore.BealData) : Prop :=
  observedDefect d = 1

/-- Exact existential negation of Q10. -/
def PrimitiveCounterexampleExists : Prop :=
  ∃ d : MCore.BealData, PrimitiveBealSolution d

/-- Q10 is exactly the nonexistence of a primitive actual Beal solution. -/
theorem materialPrimitiveExclusion_iff_noPrimitive :
    MaterialPrimitiveExclusion ↔ ¬ PrimitiveCounterexampleExists := by
  constructor
  · intro h ⟨d, hd⟩
    exact h d hd
  · intro h d hd
    exact h ⟨d, hd⟩

/-- Swap preserves the primitive locus exactly. -/
theorem primitive_swap (d : MCore.BealData) :
    PrimitiveBealSolution (swapAB d) ↔ PrimitiveBealSolution d := by
  exact primitive_swap_iff d

/--
Any genuine Q10 attack must provide a contradiction-bearing property P
from a primitive solution, and eliminate P independently.
-/
structure PrimitiveExclusionRoute where
  P : MCore.BealData -> Prop
  produce : ∀ d, PrimitiveBealSolution d -> P d
  eliminate : ∀ d, PrimitiveBealSolution d -> P d -> False

/-- A completed route closes Q10. -/
theorem close_Q10_from_route (R : PrimitiveExclusionRoute) :
    MaterialPrimitiveExclusion := by
  intro d hd
  exact R.eliminate d hd (R.produce d hd)

/--
A decomposition interface for arithmetic attacks.  No field is assumed to
exist here; an inhabitant must be constructed by real mathematics.
-/
structure ArithmeticFrontier where
  Signature : Type
  classify : MCore.BealData -> Signature
  admissible : Signature -> Prop
  primitive_implies_admissible :
    ∀ d, PrimitiveBealSolution d -> admissible (classify d)
  impossible :
    ∀ d, PrimitiveBealSolution d -> admissible (classify d) -> False

/-- Any fully material arithmetic frontier produces Q10. -/
theorem close_Q10_from_arithmetic_frontier (F : ArithmeticFrontier) :
    MaterialPrimitiveExclusion := by
  intro d hd
  exact F.impossible d hd (F.primitive_implies_admissible d hd)

/--
Negative control: swap symmetry alone cannot be the arithmetic frontier,
because the primitive locus is swap invariant.
-/
theorem swap_cannot_change_primitive_status (d : MCore.BealData)
    (hd : PrimitiveBealSolution d) :
    PrimitiveBealSolution (swapAB d) := by
  exact (primitive_swap d).2 hd

/-- OPEN_MATH leaf: construct an inhabitant of this type without assuming Q10. -/
def Q10Producer : Type :=
  { R : PrimitiveExclusionRoute // True }

end MCore.OpenMath.BealQ10
