import MCore.BealSpecification
import MCore.V5.BealPayload

namespace MCore.V5

/-- Exact mathematical residue. This is a proposition definition, not an axiom
    and not a theorem claimed by the V5 structural layer. -/
def ArithmeticResidue : Prop :=
  ∀ d : MCore.BealData, MCore.BealCounterexample d → False

/-- Dependency marker only. V5 deliberately provides no inhabitant of this
    proposition and therefore makes no FINAL_PROOF promotion. -/
def FinalProofRequires : Prop := ArithmeticResidue

theorem finalProofRequires_is_residue :
    FinalProofRequires = ArithmeticResidue := rfl

end MCore.V5
