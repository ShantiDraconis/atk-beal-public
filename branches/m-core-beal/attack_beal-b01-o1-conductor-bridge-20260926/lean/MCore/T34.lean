import MCore.T33

namespace MCore

/-- Pure divisibility encoding of the three pairwise root differences for
    the Frey cubic with roots 0, A^x, -B^y:
      0 <-> A^x        : A^x
      0 <-> -B^y       : B^y
      A^x <-> -B^y     : A^x + B^y = C^z.
    Exactly one of the three differences is divisible by p.  This is an
    arithmetic "nodal collision" package only; it does not assert a Kodaira
    type or a conductor exponent. -/
def T34FreyNodalCollision
    (a b x y p : Nat) : Prop :=
  (p ∣ a ^ x ∧
    ¬ p ∣ b ^ y ∧
    ¬ p ∣ a ^ x + b ^ y) ∨
  (p ∣ b ^ y ∧
    ¬ p ∣ a ^ x ∧
    ¬ p ∣ a ^ x + b ^ y) ∨
  (p ∣ a ^ x + b ^ y ∧
    ¬ p ∣ a ^ x ∧
    ¬ p ∣ b ^ y)

/-- Prime nondivisibility descends contrapositive through a positive power. -/
theorem T34_not_dvd_pow_of_not_dvd
    {p a n : Nat}
    (hp : IsPrime p) (hn : 0 < n)
    (hpa : ¬ p ∣ a) :
    ¬ p ∣ a ^ n := by
  intro hpow
  exact hpa (T30_prime_dvd_pow_of_pos hp hn hpow)

/-- The T33 odd-prime local input plus pairwise primitiveness forces exactly
    one collision among the three Frey roots modulo p, expressed entirely by
    divisibility of their pairwise differences. -/
theorem T34_reduction_input_to_nodal_collision
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hInput : T33OddPrimeReductionInput a b c x y z p) :
    T34FreyNodalCollision a b x y p := by
  have hp : IsPrime p := hInput.1
  have hsupp : p ∣ a ∨ p ∣ b ∨ p ∣ c := hInput.2.2.2.2
  rcases hsupp with hpa | hpb | hpc
  ·
    have hAx : p ∣ a ^ x := T11_dvd_pow_of_dvd hx hpa
    have hnotb : ¬ p ∣ b := by
      intro hpb
      exact hpw.1 ⟨p, hp.1, hpa, hpb⟩
    have hnotBy : ¬ p ∣ b ^ y :=
      T34_not_dvd_pow_of_not_dvd hp hy hnotb
    have hnotc : ¬ p ∣ c := by
      intro hpc
      exact hpw.2.1 ⟨p, hp.1, hpa, hpc⟩
    have hnotCz : ¬ p ∣ c ^ z :=
      T34_not_dvd_pow_of_not_dvd hp hz hnotc
    have hnotSum : ¬ p ∣ a ^ x + b ^ y := by
      intro hsum
      have hcz : p ∣ c ^ z := by
        rw [← heq]
        exact hsum
      exact hnotCz hcz
    exact Or.inl ⟨hAx, hnotBy, hnotSum⟩
  ·
    have hBy : p ∣ b ^ y := T11_dvd_pow_of_dvd hy hpb
    have hnota : ¬ p ∣ a := by
      intro hpa
      exact hpw.1 ⟨p, hp.1, hpa, hpb⟩
    have hnotAx : ¬ p ∣ a ^ x :=
      T34_not_dvd_pow_of_not_dvd hp hx hnota
    have hnotc : ¬ p ∣ c := by
      intro hpc
      exact hpw.2.2 ⟨p, hp.1, hpb, hpc⟩
    have hnotCz : ¬ p ∣ c ^ z :=
      T34_not_dvd_pow_of_not_dvd hp hz hnotc
    have hnotSum : ¬ p ∣ a ^ x + b ^ y := by
      intro hsum
      have hcz : p ∣ c ^ z := by
        rw [← heq]
        exact hsum
      exact hnotCz hcz
    exact Or.inr (Or.inl ⟨hBy, hnotAx, hnotSum⟩)
  ·
    have hCz : p ∣ c ^ z := T11_dvd_pow_of_dvd hz hpc
    have hSum : p ∣ a ^ x + b ^ y := by
      rw [heq]
      exact hCz
    have hnota : ¬ p ∣ a := by
      intro hpa
      exact hpw.2.1 ⟨p, hp.1, hpa, hpc⟩
    have hnotb : ¬ p ∣ b := by
      intro hpb
      exact hpw.2.2 ⟨p, hp.1, hpb, hpc⟩
    have hnotAx : ¬ p ∣ a ^ x :=
      T34_not_dvd_pow_of_not_dvd hp hx hnota
    have hnotBy : ¬ p ∣ b ^ y :=
      T34_not_dvd_pow_of_not_dvd hp hy hnotb
    exact Or.inr (Or.inr ⟨hSum, hnotAx, hnotBy⟩)

def T34FreyNodalCollisionConstraint
    (a b c x y z : Nat) : Prop :=
  ∀ p : Nat,
    T33OddPrimeReductionInput a b c x y z p →
    T34FreyNodalCollision a b x y p

def T34FreyNodalCollisionCandidate : Prop :=
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
    T24FreyDiscriminantConstraint a b c x y z ∧
    T25FreyTwoAdicDepthConstraint a b c x y z ∧
    T27FreyDivisorDepthConstraint a b c x y z ∧
    T28FreyPrimeSupportConstraint a b c x y z ∧
    T30FreyBasePrimeSupportConstraint a b c x y z ∧
    T31FreyRadicalSupportConstraint a b c x y z ∧
    T32FreyC4CoprimeConstraint a b c x y z ∧
    T33OddPrimeReductionInputConstraint a b c x y z ∧
    T34FreyNodalCollisionConstraint a b c x y z

theorem T34_T33_to_nodal_collision :
    T33OddPrimeReductionInputCandidate → T34FreyNodalCollisionCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, h33⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  refine ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, h33, ?_⟩
  intro p hInput
  exact T34_reduction_input_to_nodal_collision
    hx0 hy0 hz0 heq hpw hInput

theorem T34_nodal_collision_to_T33 :
    T34FreyNodalCollisionCandidate → T33OddPrimeReductionInputCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, h33, _⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw, hpar,
    h44, h14, h15, h16, h17, h18a, h18b, h19, h20, h21, h22, h23,
    h24, h25, h27, h28, h30, h31, h32, h33⟩

theorem T34_candidate_iff_nodal_collision :
    T33OddPrimeReductionInputCandidate ↔ T34FreyNodalCollisionCandidate :=
  ⟨T34_T33_to_nodal_collision, T34_nodal_collision_to_T33⟩

def T34FreyNodalCollisionScientificFrontier : Prop :=
  ¬ T34FreyNodalCollisionCandidate

theorem T34_beal_iff_nodal_collision_frontier :
    BealConjecture ↔ T34FreyNodalCollisionScientificFrontier := by
  rw [T33_beal_iff_reduction_input_frontier]
  unfold T33OddPrimeReductionInputScientificFrontier
    T34FreyNodalCollisionScientificFrontier
  exact not_congr T34_candidate_iff_nodal_collision

#print axioms MCore.T34_not_dvd_pow_of_not_dvd
#print axioms MCore.T34_reduction_input_to_nodal_collision
#print axioms MCore.T34_candidate_iff_nodal_collision
#print axioms MCore.T34_beal_iff_nodal_collision_frontier

end MCore
