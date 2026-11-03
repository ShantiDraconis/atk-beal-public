import MCore.V5.OmegaPoint
import MCore.V5.OmegaBottom

namespace MCore.V5

inductive ExtendedElem (α : Type u) : Type u where
  | ofNat : Nat → ExtendedElem α
  | omega : OmegaPoint α → ExtendedElem α
  | bot : OmegaBottom α → ExtendedElem α
deriving DecidableEq, Repr

def add : ExtendedElem α → ExtendedElem α → ExtendedElem α
  | .bot b, _ => .bot b
  | _, .bot b => .bot b
  | .omega o, _ => .omega o
  | _, .omega o => .omega o
  | .ofNat m, .ofNat n => .ofNat (m + n)

def mul : ExtendedElem α → ExtendedElem α → ExtendedElem α
  | .ofNat 0, .omega (.mk a) => .bot (.mk a)
  | .omega (.mk a), .ofNat 0 => .bot (.mk a)
  | .bot b, _ => .bot b
  | _, .bot b => .bot b
  | .omega o, _ => .omega o
  | _, .omega o => .omega o
  | .ofNat m, .ofNat n => .ofNat (m * n)

@[simp] theorem zero_mul_omega_eq_bot (a : α) :
    mul (.ofNat 0) (.omega (omegaPoint a)) = .bot (omegaBottom a) := rfl

@[simp] theorem bot_absorbs_add (b : OmegaBottom α) (x : ExtendedElem α) :
    add (.bot b) x = .bot b := rfl

theorem omega_ne_bot (a : α) :
    (ExtendedElem.omega (omegaPoint a) : ExtendedElem α) ≠ .bot (omegaBottom a) := by
  intro h
  cases h

abbrev WOmegaModel := ExtendedElem Unit

theorem model_distinguishes :
    (ExtendedElem.ofNat 0 : WOmegaModel) ≠ .bot (omegaBottom ()) := by
  intro h
  cases h

end MCore.V5
