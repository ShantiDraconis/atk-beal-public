import MCore.T23

namespace MCore

/-- Algebraic discriminant kernel for the Frey model
    Y^2 = X (X - A^x) (X + B^y).

    For roots 0, A^x, -B^y, the elliptic discriminant is
    16 * (A^x)^2 * (B^y)^2 * (A^x + B^y)^2.

    T24 deliberately records only this exact algebraic identity. It does not
    assert modularity, semistability, conductor minimality, level lowering, or
    newform elimination. -/
def T24FreyDiscriminantKernel
    (a b x y : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (a ^ x + b ^ y) ^ 2

/-- Beal-equation normal form of the same discriminant kernel. -/
def T24FreyDiscriminantBeal
    (a b c x y z : Nat) : Nat :=
  16 * (a ^ x) ^ 2 * (b ^ y) ^ 2 * (c ^ z) ^ 2

/-- The Beal equation rewrites the Frey discriminant exactly.
    This is the first formally valid bridge from the reduced Diophantine
    candidate into Frey-curve algebra. -/
theorem T24_frey_discriminant_rewrite
    {a b c x y z : Nat}
    (heq : a ^ x + b ^ y = c ^ z) :
    T24FreyDiscriminantKernel a b x y =
      T24FreyDiscriminantBeal a b c x y z := by
  unfold T24FreyDiscriminantKernel T24FreyDiscriminantBeal
  rw [heq]

/-- Exact T24 payload. It is intentionally weaker than any modular-method
    conclusion: it stores only the discriminant rewrite justified by the
    original Beal equation. -/
def T24FreyDiscriminantConstraint
    (a b c x y z : Nat) : Prop :=
  T24FreyDiscriminantKernel a b x y =
    T24FreyDiscriminantBeal a b c x y z

def T24FreyDiscriminantCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c ∧
    T12ExactlyOneEven a b c ∧
    (T12Even c → ¬ (x = 4 ∧ y = 4)) ∧
    T14CResidueConstraint a b c x y z ∧
    T15CBaseResidueConstraint a b c x y z ∧
    T16CEightConstraint a b c x y z ∧
    T17CEvenClassifier a b c x y z ∧
    T18AEvenClassifier a b c x y z ∧
    T18BEvenClassifier a b c x y z ∧
    T19VariableTwoAdicConstraint a b c x y z ∧
    T20TwoAdicDepthConstraint a b c x y z ∧
    T21EqualExponentFactorConstraint a b c x y z ∧
    T22EqualOddExponentTwoAdicConstraint a b c x y z ∧
    T23EqualOddGapDepthConstraint a b c x y z ∧
    T24FreyDiscriminantConstraint a b c x y z

theorem T24_T23_to_frey_discriminant :
    T23EqualOddGapDepthCandidate → T24FreyDiscriminantCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23⟩
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, ?_⟩
  exact T24_frey_discriminant_rewrite heq

theorem T24_frey_discriminant_to_T23 :
    T24FreyDiscriminantCandidate → T23EqualOddGapDepthCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23⟩

theorem T24_candidate_iff_frey_discriminant :
    T23EqualOddGapDepthCandidate ↔ T24FreyDiscriminantCandidate :=
  ⟨T24_T23_to_frey_discriminant, T24_frey_discriminant_to_T23⟩

def T24FreyDiscriminantScientificFrontier : Prop :=
  ¬ T24FreyDiscriminantCandidate

theorem T24_beal_iff_frey_discriminant_frontier :
    BealConjecture ↔ T24FreyDiscriminantScientificFrontier := by
  rw [T23_beal_iff_equal_odd_gap_depth_frontier]
  unfold T23EqualOddGapDepthScientificFrontier
    T24FreyDiscriminantScientificFrontier
  exact not_congr T24_candidate_iff_frey_discriminant

#print axioms MCore.T24_frey_discriminant_rewrite
#print axioms MCore.T24_candidate_iff_frey_discriminant
#print axioms MCore.T24_beal_iff_frey_discriminant_frontier

end MCore
