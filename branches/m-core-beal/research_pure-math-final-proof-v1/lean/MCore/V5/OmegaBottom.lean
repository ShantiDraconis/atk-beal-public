namespace MCore.V5

/-- Tagged indeterminate state. It carries, rather than erases, its payload. -/
inductive OmegaBottom (α : Type u) : Type u where
  | mk : α → OmegaBottom α
deriving DecidableEq, Repr

namespace OmegaBottom
def payload : OmegaBottom α → α
  | .mk a => a
end OmegaBottom

def omegaBottom (a : α) : OmegaBottom α := .mk a

@[simp] theorem omegaBottom_payload (a : α) :
    (omegaBottom a).payload = a := rfl

end MCore.V5
