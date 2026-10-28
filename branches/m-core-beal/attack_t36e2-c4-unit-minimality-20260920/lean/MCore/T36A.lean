import MCore.T36

namespace MCore

/-!
T36A — THREE SEMANTIC LEMMAS FAIL-PROOF

This module decomposes the unique T36 semantic criterion into exactly three
independent local obligations.  It proves only the logical assembly and does
not assert any elliptic-curve theorem by name.

A later Mathlib integration must instantiate these predicates with genuine
Weierstrass/DVR reduction semantics and prove the three obligations.
-/

/-- Obligation A: the certified arithmetic package implies multiplicative
    reduction at the same Frey datum and odd prime. -/
def T36AMultiplicativeLemma
    (S : T36OddLocalSemantics) : Prop :=
  ∀ a b c x y z p : Nat,
    T36OddLocalArithmeticPackage a b c x y z p →
    S.multiplicativeReductionAt a b c x y z p

/-- Obligation B: the same arithmetic package implies that the chosen local
    Frey Weierstrass model is minimal at p. -/
def T36AMinimalityLemma
    (S : T36OddLocalSemantics) : Prop :=
  ∀ a b c x y z p : Nat,
    T36OddLocalArithmeticPackage a b c x y z p →
    S.minimalAt a b c x y z p

/-- Obligation C: after the local model/reduction theory is fixed, the same
    package implies local conductor exponent one. -/
def T36AConductorExponentOneLemma
    (S : T36OddLocalSemantics) : Prop :=
  ∀ a b c x y z p : Nat,
    T36OddLocalArithmeticPackage a b c x y z p →
    S.conductorExponentOneAt a b c x y z p

/-- Typed bundle containing precisely the three missing T36 semantic lemmas. -/
structure T36AThreeSemanticLemmas
    (S : T36OddLocalSemantics) : Prop where
  multiplicative : T36AMultiplicativeLemma S
  minimality : T36AMinimalityLemma S
  conductorExponentOne : T36AConductorExponentOneLemma S

/-- The central fail-proof: the original T36 semantic criterion is equivalent
    to supplying exactly the three semantic lemmas above. -/
theorem T36A_criterion_iff_three_semantic_lemmas
    (S : T36OddLocalSemantics) :
    T36OddLocalSemanticCriterion S ↔
      T36AThreeSemanticLemmas S := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a b c x y z p hPkg
      exact (h a b c x y z p hPkg).1
    · intro a b c x y z p hPkg
      exact (h a b c x y z p hPkg).2.1
    · intro a b c x y z p hPkg
      exact (h a b c x y z p hPkg).2.2
  · intro h a b c x y z p hPkg
    exact ⟨
      h.multiplicative a b c x y z p hPkg,
      h.minimality a b c x y z p hPkg,
      h.conductorExponentOne a b c x y z p hPkg
    ⟩

/-- Consequently a genuine proof of all three obligations closes the entire
    T36 semantic goal through the already-certified T36 equivalence. -/
theorem T36A_three_lemmas_close_T36
    {S : T36OddLocalSemantics}
    (h : T36AThreeSemanticLemmas S) :
    T36OddLocalSemanticGoal S := by
  apply (T36_semantic_goal_iff_criterion S).2
  exact (T36A_criterion_iff_three_semantic_lemmas S).2 h

/-- A fail-closed three-way state: none of the semantic obligations is promoted
    merely because the arithmetic package is GREEN. -/
structure T36ASemanticGapState where
  multiplicative : T36GapState
  minimality : T36GapState
  conductorExponentOne : T36GapState

def T36ACurrentSemanticGapState : T36ASemanticGapState where
  multiplicative := .openBridge
  minimality := .openBridge
  conductorExponentOne := .openBridge

#print axioms MCore.T36A_criterion_iff_three_semantic_lemmas
#print axioms MCore.T36A_three_lemmas_close_T36

end MCore
