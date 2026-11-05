import MCore.Material.Closure
namespace ATK.Beal
abbrev Material (C M : Type) [LT M] : Prop :=
  MCore.Material.MaterialBealDescent C M

theorem producer_of_concrete {C M : Type} [LT M]
    (h : MCore.Material.BealDescentClosure C M) : Material C M := ⟨h⟩
end ATK.Beal
#print axioms ATK.Beal.producer_of_concrete
