import MCore.T59
import MCore.T47
import MCore.T50

namespace MCore

/--
Concrete classification of every parity-normalized reduced Beal counterexample.

The first two branches are the classical equal-exponent branches:
* equal odd-prime signature;
* all exponents equal 4.

Every remaining branch is exactly a concrete T59 residual candidate, with no
additional existential arithmetic payload.
-/
inductive T59ParityPartition where
  | equalOddPrime
      (a b c x y z : Nat)
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (hx : T7ReducedExponent x)
      (hy : T7ReducedExponent y)
      (hz : T7ReducedExponent z)
      (heq : a ^ x + b ^ y = c ^ z)
      (hpw : T11PairwisePrimitive a b c)
      (hpar : T12ExactlyOneEven a b c)
      (hsig : T45EqualOddPrimeSignature x y z)
  | allFour
      (a b c : Nat)
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (heq : a ^ 4 + b ^ 4 = c ^ 4)
      (hpw : T11PairwisePrimitive a b c)
      (hpar : T12ExactlyOneEven a b c)
  | residual (d : T59ResidualCandidate)

/--
Every T12 parity-reduced candidate belongs to exactly one useful downstream
class: equal odd-prime, all-four, or the T59 mixed residual domain.
-/
noncomputable def T12_to_T59_partition
    (h : T12ParityReducedCandidate) :
    T59ParityPartition := by
  classical
  rcases h with
    ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar⟩
  by_cases hEq : T45EqualOddPrimeSignature x y z
  · exact .equalOddPrime a b c x y z ha hb hc hx hy hz heq hpw hpar hEq
  · have hMixed : T45MixedReducedSignature x y z :=
      ⟨hx, hy, hz, hEq⟩
    by_cases h4 : T49AllFour x y z
    · rcases h4 with ⟨rfl, rfl, rfl⟩
      exact .allFour a b c ha hb hc heq hpw hpar
    · exact .residual
        { a := a
          b := b
          c := c
          x := x
          y := y
          z := z
          a_pos := ha
          b_pos := hb
          c_pos := hc
          x_reduced := hx
          y_reduced := hy
          z_reduced := hz
          equation := heq
          pairwisePrimitive := hpw
          exactlyOneEven := hpar
          mixed := hMixed
          notAllFour := h4 }

/-- Elimination contract for the equal odd-prime branch. -/
def T59EqualOddPrimeEliminator : Prop :=
  ∀ a b c x y z : Nat,
    0 < a → 0 < b → 0 < c →
    T7ReducedExponent x →
    T7ReducedExponent y →
    T7ReducedExponent z →
    a ^ x + b ^ y = c ^ z →
    T11PairwisePrimitive a b c →
    T12ExactlyOneEven a b c →
    T45EqualOddPrimeSignature x y z →
    False

/-- Elimination contract for the all-four branch. -/
def T59AllFourEliminator : Prop :=
  ∀ a b c : Nat,
    0 < a → 0 < b → 0 < c →
    a ^ 4 + b ^ 4 = c ^ 4 →
    T11PairwisePrimitive a b c →
    T12ExactlyOneEven a b c →
    False

/-- Elimination contract for the genuine mixed residual domain. -/
def T59ResidualEliminator : Prop :=
  ∀ d : T59ResidualCandidate, False

/--
The three eliminators remove every T12 parity-reduced counterexample.
This is a strict decomposition of the Beal material frontier: no CommonPrime,
GCD lower bound, or Beal endpoint is stored in any eliminator.
-/
theorem T59_three_branch_elimination_closes_parity_frontier
    (hEq : T59EqualOddPrimeEliminator)
    (h4 : T59AllFourEliminator)
    (hResidual : T59ResidualEliminator) :
    T12ParityScientificFrontier := by
  intro hCandidate
  cases T12_to_T59_partition hCandidate with
  | equalOddPrime a b c x y z ha hb hc hx hy hz heq hpw hpar hsig =>
      exact hEq a b c x y z ha hb hc hx hy hz heq hpw hpar hsig
  | allFour a b c ha hb hc heq hpw hpar =>
      exact h4 a b c ha hb hc heq hpw hpar
  | residual d =>
      exact hResidual d

/--
Consequently, the same three branch eliminators close Beal through the already
certified T12 equivalence.
-/
theorem T59_three_branch_elimination_closes_beal
    (hEq : T59EqualOddPrimeEliminator)
    (h4 : T59AllFourEliminator)
    (hResidual : T59ResidualEliminator) :
    BealConjecture :=
  T12_beal_iff_parity_frontier.mpr
    (T59_three_branch_elimination_closes_parity_frontier hEq h4 hResidual)

/--
Residual-only corollary after the two classical branches have independently
been supplied.
-/
theorem T59_residual_is_only_remaining_branch
    (hEq : T59EqualOddPrimeEliminator)
    (h4 : T59AllFourEliminator) :
    T59ResidualEliminator → BealConjecture :=
  fun hResidual =>
    T59_three_branch_elimination_closes_beal hEq h4 hResidual

#print axioms MCore.T12_to_T59_partition
#print axioms MCore.T59_three_branch_elimination_closes_parity_frontier
#print axioms MCore.T59_three_branch_elimination_closes_beal
#print axioms MCore.T59_residual_is_only_remaining_branch

end MCore


namespace MCore

/-- Remaining FLT content after using Mathlib's certified exponent 3 branch. -/
def T59FLTBeyondThree : Prop :=
  ∀ ell : Nat,
    IsPrime ell →
    3 < ell →
    T47FLTAt ell

/-- Mathlib FLT(3) plus a certificate for all odd primes above 3 yields the
full equal-odd-prime family certificate required by T47. -/
def T59_equalPrimeFamily_of_beyondThree
    (hBeyond : T59FLTBeyondThree) :
    T47FLTFamilyCertificate where
  closes := by
    intro ell hp h2
    by_cases h3 : ell = 3
    · subst ell
      exact T50_mathlib_flt3
    · have hgt3 : 3 < ell := by
        omega
      exact hBeyond ell hp hgt3

/-- The all-four branch is already discharged by the frozen Mathlib FLT(4)
bridge; no additional Beal-specific material is required here. -/
theorem T59_allFourEliminator_proved :
    T59AllFourEliminator := by
  intro a b c ha hb hc heq hpw hpar
  exact T50_mathlib_flt4 a b c ha hb hc heq

/-- The only equal-prime material not supplied by the current Mathlib bridge
is FLT at odd prime exponents strictly above 3. -/
theorem T59_equalOddPrimeEliminator_of_beyondThree
    (hBeyond : T59FLTBeyondThree) :
    T59EqualOddPrimeEliminator := by
  intro a b c x y z ha hb hc hx hy hz heq hpw hpar hsig
  exact T47_family_certificate_eliminates_equal_prime_signature
    ha hb hc hx hy hz heq hsig
    (T59_equalPrimeFamily_of_beyondThree hBeyond)

/--
Compressed Beal modular frontier:
after certified exponent reduction, primitiveness/parity normalization,
Mathlib FLT(3), and Mathlib FLT(4), only two independent materials remain:
1. FLT for odd prime exponents > 3 on the equal-prime branch;
2. elimination of every T59 mixed residual candidate.
-/
theorem T59_beyondThree_and_residual_close_beal
    (hBeyond : T59FLTBeyondThree)
    (hResidual : T59ResidualEliminator) :
    BealConjecture :=
  T59_three_branch_elimination_closes_beal
    (T59_equalOddPrimeEliminator_of_beyondThree hBeyond)
    T59_allFourEliminator_proved
    hResidual

#print axioms MCore.T59_equalPrimeFamily_of_beyondThree
#print axioms MCore.T59_allFourEliminator_proved
#print axioms MCore.T59_equalOddPrimeEliminator_of_beyondThree
#print axioms MCore.T59_beyondThree_and_residual_close_beal

end MCore
