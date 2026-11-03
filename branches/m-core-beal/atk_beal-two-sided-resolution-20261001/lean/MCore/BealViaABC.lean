import MCore.BealStatementFrozen

namespace MCore

/-!
ABC CONDITIONAL FAST LANE

`ABCStatement` is deliberately a parameter here rather than an invented local
definition of abc.  A later canonical abc formalization may instantiate it.
The reduction is honest and fail-closed: ABC alone is not enough; one must
also provide an effective finite-bound reduction and a verified finite check.
-/

/-- Effective consequence needed from a chosen canonical ABC statement.
    Under ABC, every Beal datum above `bound` has a common prime. -/
structure ABCBealFiniteReduction (ABCStatement : Prop) where
  bound : Nat
  outside :
    ABCStatement →
    ∀ d : BealData, bound < d.c → CommonPrime d.a d.b d.c

/-- Verified finite search below the effective bound. -/
structure BealFiniteCheck (N : Nat) where
  checked :
    ∀ d : BealData, d.c ≤ N → CommonPrime d.a d.b d.c

/-- Exact conditional composition theorem.
    This theorem has no hidden reduction from ABC: the reduction object and
    finite check are explicit inputs. -/
theorem Beal_of_ABC_and_finite_check
    {ABCStatement : Prop}
    (hABC : ABCStatement)
    (R : ABCBealFiniteReduction ABCStatement)
    (C : BealFiniteCheck R.bound) :
    BealConjecture := by
  intro d
  by_cases h : d.c ≤ R.bound
  · exact C.checked d h
  · have hgt : R.bound < d.c := Nat.lt_of_not_ge h
    exact R.outside hABC d hgt

/-- Typed conditional proof package consumed by an EGC.
    It cannot be inhabited from ABC alone. -/
structure BealABCConditionalProof (ABCStatement : Prop) where
  abc : ABCStatement
  reduction : ABCBealFiniteReduction ABCStatement
  finiteCheck : BealFiniteCheck reduction.bound

def BealABCConditionalProof.toBeal
    {ABCStatement : Prop}
    (P : BealABCConditionalProof ABCStatement) :
    BealConjecture :=
  Beal_of_ABC_and_finite_check P.abc P.reduction P.finiteCheck

#print axioms MCore.Beal_of_ABC_and_finite_check
#print axioms MCore.BealABCConditionalProof.toBeal

end MCore
