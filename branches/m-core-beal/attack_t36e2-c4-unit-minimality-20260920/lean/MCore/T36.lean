import MCore.T35

namespace MCore

/-- Complete arithmetic package already available before invoking any semantic
    elliptic-curve reduction theorem at an odd prime. -/
structure T36OddLocalArithmeticPackage
    (a b c x y z p : Nat) : Prop where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  equation : a ^ x + b ^ y = c ^ z
  pairwisePrimitive : T11PairwisePrimitive a b c
  input : T33OddPrimeReductionInput a b c x y z p
  nodalCollision : T34FreyNodalCollision a b x y p

/-- T33 + T34 already construct the entire arithmetic package. -/
theorem T36_arithmetic_package_of_input
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hInput : T33OddPrimeReductionInput a b c x y z p) :
    T36OddLocalArithmeticPackage a b c x y z p := by
  refine ⟨hx, hy, hz, heq, hpw, hInput, ?_⟩
  exact T34_reduction_input_to_nodal_collision
    hx hy hz heq hpw hInput

/-- Global statement that the arithmetic side of T36 is prepared for every
    odd discriminant prime satisfying the already-certified hypotheses. -/
def T36ArithmeticPreparation : Prop :=
  ∀ a b c x y z p : Nat,
    0 < x →
    0 < y →
    0 < z →
    a ^ x + b ^ y = c ^ z →
    T11PairwisePrimitive a b c →
    T33OddPrimeReductionInput a b c x y z p →
    T36OddLocalArithmeticPackage a b c x y z p

theorem T36_arithmetic_preparation_proved :
    T36ArithmeticPreparation := by
  intro a b c x y z p hx hy hz heq hpw hInput
  exact T36_arithmetic_package_of_input
    hx hy hz heq hpw hInput

/-- Semantic interface intentionally left abstract until a genuine formal
    elliptic-curve reduction theory is imported.  The predicates must refer to
    the same Frey datum (a,b,c,x,y,z) and local prime p. -/
structure T36OddLocalSemantics where
  multiplicativeReductionAt :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop
  minimalAt :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop
  conductorExponentOneAt :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop

def T36OddLocalSemanticTarget
    (S : T36OddLocalSemantics)
    (a b c x y z p : Nat) : Prop :=
  S.multiplicativeReductionAt a b c x y z p ∧
  S.minimalAt a b c x y z p ∧
  S.conductorExponentOneAt a b c x y z p

/-- The exact remaining scientific theorem at T36:
    the already-proved arithmetic package implies the semantic local-reduction
    conclusions.  T36 does not assert this criterion. -/
def T36OddLocalSemanticCriterion
    (S : T36OddLocalSemantics) : Prop :=
  ∀ a b c x y z p : Nat,
    T36OddLocalArithmeticPackage a b c x y z p →
    T36OddLocalSemanticTarget S a b c x y z p

/-- Direct formulation of the same missing theorem from the pre-T36 inputs. -/
def T36OddLocalSemanticGoal
    (S : T36OddLocalSemantics) : Prop :=
  ∀ a b c x y z p : Nat,
    0 < x →
    0 < y →
    0 < z →
    a ^ x + b ^ y = c ^ z →
    T11PairwisePrimitive a b c →
    T33OddPrimeReductionInput a b c x y z p →
    T36OddLocalSemanticTarget S a b c x y z p

/-- FAIL-PROOF reduction of the odd-local OPEN_BRIDGE:
    the direct semantic goal is equivalent to one and only one missing
    criterion on the complete arithmetic package. -/
theorem T36_semantic_goal_iff_criterion
    (S : T36OddLocalSemantics) :
    T36OddLocalSemanticGoal S ↔
      T36OddLocalSemanticCriterion S := by
  constructor
  · intro hGoal a b c x y z p hPkg
    exact hGoal a b c x y z p
      hPkg.x_pos hPkg.y_pos hPkg.z_pos
      hPkg.equation hPkg.pairwisePrimitive hPkg.input
  · intro hCriterion a b c x y z p hx hy hz heq hpw hInput
    apply hCriterion a b c x y z p
    exact T36_arithmetic_package_of_input
      hx hy hz heq hpw hInput

/-- A genuine scientific certificate for T36 consists precisely of a proof of
    the semantic criterion above. -/
structure T36ScientificOddLocalCertificate
    (S : T36OddLocalSemantics) : Prop where
  criterion : T36OddLocalSemanticCriterion S

theorem T36_scientific_certificate_closes_semantic_goal
    {S : T36OddLocalSemantics}
    (c : T36ScientificOddLocalCertificate S) :
    T36OddLocalSemanticGoal S :=
  (T36_semantic_goal_iff_criterion S).2 c.criterion

/-- Existing ledger-level certificate retained for the T35/T42 fail-closed
    bundle.  It cannot be constructed from the arithmetic preparation alone. -/
structure T36OddLocalReductionCertificate (G : T35GapLedger) where
  bridge : T35OddLocalReductionBridge G

theorem T36_certificate_discharges_odd_local
    {G : T35GapLedger}
    (c : T36OddLocalReductionCertificate G) :
    T35OddLocalReductionBridge G :=
  c.bridge

inductive T36GapState
  | openBridge
  | certified

/-- Correct current scientific state: arithmetic preparation is proved, while
    the semantic elliptic-reduction criterion remains external/open. -/
def T36OddLocalReductionState : T36GapState :=
  .openBridge

#print axioms MCore.T36_arithmetic_package_of_input
#print axioms MCore.T36_arithmetic_preparation_proved
#print axioms MCore.T36_semantic_goal_iff_criterion
#print axioms MCore.T36_scientific_certificate_closes_semantic_goal
#print axioms MCore.T36_certificate_discharges_odd_local

end MCore
