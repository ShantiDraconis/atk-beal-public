namespace MCore.V5

/-- Tagged omega point. It is a new type and is not identified with division by zero. -/
inductive OmegaPoint (α : Type u) : Type u where
  | mk : α → OmegaPoint α
deriving DecidableEq, Repr

namespace OmegaPoint
def payload : OmegaPoint α → α
  | .mk a => a
end OmegaPoint

def omegaPoint (a : α) : OmegaPoint α := .mk a

@[simp] theorem omegaPoint_payload (a : α) :
    (omegaPoint a).payload = a := rfl

end MCore.V5
