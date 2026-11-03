import MCore.B01DenseScientificFrontier
import MCore.B02DenseScientificFrontier
import MCore.BealFastExternalEndpoint
import MCore.BealFinalExternalAggregator

namespace MCore

/-! BEAL BOUNDARY CONNECTIVITY MAP

This file makes the reusable proof graph explicit.  It does not inhabit any
OPEN_MATH frontier; it records the exact typed transitions already proved.
-/

inductive BealBoundary where
  | localArithmetic
  | multiplicativeReduction
  | conductorAndLevel
  | residualNewform
  | commonDivisorEndpoint
  | commonPrimeEndpoint
  | proofCertificate
  deriving DecidableEq, Repr

/-- GREEN: T60 arithmetic packets feed the genuine Mathlib multiplicative
    reduction bridge already proved in PostT36EConductorBridge. -/
theorem boundary_local_to_multiplicative
    (d : T59ResidualCandidate) :
    T60GenuineOddMultiplicativeReduction d :=
  T60_every_candidate_has_genuine_odd_multiplicative_reduction d

/-- OPEN_MATH boundary type: exact conductor + lowering semantics. -/
def BoundaryConductorLevel : Type := B01DenseUniversal

/-- OPEN_MATH boundary type: residual coverage + five family eliminations. -/
def BoundaryResidualNewform : Type := B02DenseScientificInhabitant

/-- Exact residual aggregation once B02 data exists. -/
theorem boundary_residual_to_newform_elimination
    (H : BoundaryResidualNewform) :
    T44AllNewformsEliminated H.semantics.Survives :=
  b02_dense_eliminates_all H

/-- Shortest exact terminal boundary: nontrivial common divisor for every
    admissible Beal datum. -/
def BoundaryCommonDivisor : Type := BealCommonDivisorProducer

/-- K10 is the already-GREEN conversion from the common-divisor boundary to
    the original common-prime formulation. -/
theorem boundary_commonDivisor_to_commonPrime
    (P : BoundaryCommonDivisor) :
    ∀ d : BealData, CommonPrime d.a d.b d.c :=
  commonDivisorProducer_to_commonPrime P

/-- Terminal proof conversion. -/
theorem boundary_commonDivisor_to_beal
    (P : BoundaryCommonDivisor) : BealConjecture :=
  commonDivisorProducer_closes_beal P

def boundary_commonDivisor_to_proofCertificate
    (P : BoundaryCommonDivisor) : BealProofCertificate :=
  ⟨boundary_commonDivisor_to_beal P⟩

/-- Exact logical equivalence of the shortest terminal producer and Beal. -/
theorem boundary_terminal_exact :
    BealConjecture ↔ Nonempty BoundaryCommonDivisor :=
  beal_iff_commonDivisorProducer

#print axioms MCore.boundary_local_to_multiplicative
#print axioms MCore.boundary_residual_to_newform_elimination
#print axioms MCore.boundary_commonDivisor_to_commonPrime
#print axioms MCore.boundary_commonDivisor_to_beal
#print axioms MCore.boundary_terminal_exact

end MCore
