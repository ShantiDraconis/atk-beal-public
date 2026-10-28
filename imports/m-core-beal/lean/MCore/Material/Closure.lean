import MCore
namespace MCore.Material
structure BealDescentClosure (Counterexample Measure : Type) [LT Measure] where
  measure : Counterexample → Measure
  transform : Counterexample → Counterexample
  primitivePreserved : Prop
  strictDecrease : ∀ c, measure (transform c) < measure c
  primitivePreserved_proof : primitivePreserved

def MaterialBealDescent (Counterexample Measure : Type) [LT Measure] : Prop :=
  Nonempty (BealDescentClosure Counterexample Measure)
end MCore.Material
