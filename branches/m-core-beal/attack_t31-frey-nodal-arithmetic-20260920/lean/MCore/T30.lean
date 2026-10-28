import MCore.T29

namespace MCore

/-- Raw odd bad-prime condition for the integral Frey model, expressed purely
    arithmetically through its discriminant. -/
def T30RawOddBadPrime
    (a b c x y z p : Nat) : Prop :=
  IsPrime p ∧
  p ≠ 2 ∧
  p ∣ T24FreyDiscriminantBeal a b c x y z

/-- Arithmetic multiplicative pattern: an odd prime divides the raw
    discriminant but not c4. This is exactly the input consumed by the
    standard local reduction criterion; T30 does not itself assert an elliptic
    reduction type or conductor exponent. -/
def T30ArithmeticMultiplicativePrime
    (a b c x y z p : Nat) : Prop :=
  T30RawOddBadPrime a b c x y z p ∧
  ¬ p ∣ T29FreyC4 a b x y

theorem T30_raw_bad_implies_arithmetic_multiplicative
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hbad : T30RawOddBadPrime a b c x y z p) :
    T30ArithmeticMultiplicativePrime a b c x y z p := by
  rcases hbad with ⟨hp, hp2, hDelta⟩
  exact ⟨⟨hp, hp2, hDelta⟩,
    T29_frey_odd_support_not_c4 hp hp2 hx hy hz heq hpw hDelta⟩

theorem T30_arithmetic_multiplicative_implies_raw_bad
    {a b c x y z p : Nat}
    (h : T30ArithmeticMultiplicativePrime a b c x y z p) :
    T30RawOddBadPrime a b c x y z p :=
  h.1

/-- On the primitive Beal/Frey locus, raw odd bad support and the arithmetic
    multiplicative pattern are equivalent. -/
theorem T30_raw_bad_iff_arithmetic_multiplicative
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c) :
    T30RawOddBadPrime a b c x y z p ↔
      T30ArithmeticMultiplicativePrime a b c x y z p := by
  constructor
  · exact T30_raw_bad_implies_arithmetic_multiplicative hx hy hz heq hpw
  · exact T30_arithmetic_multiplicative_implies_raw_bad

/-- Exact base-support classification of raw odd bad primes. -/
theorem T30_raw_bad_iff_exactly_one_base
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hpw : T11PairwisePrimitive a b c) :
    T30RawOddBadPrime a b c x y z p ↔
      IsPrime p ∧ p ≠ 2 ∧ T28ExactlyOneBaseSupport p a b c := by
  constructor
  · rintro ⟨hp, hp2, hDelta⟩
    exact ⟨hp, hp2,
      T28_frey_odd_prime_exactly_one_base hp hp2 hx hy hz hpw hDelta⟩
  · rintro ⟨hp, hp2, hexact⟩
    refine ⟨hp, hp2, ?_⟩
    rcases hexact with ha | hb | hc
    · exact T28_prime_of_a_divides_frey_discriminant hx ha.1
    · exact T28_prime_of_b_divides_frey_discriminant hy hb.2.1
    · exact T28_prime_of_c_divides_frey_discriminant hz hc.2.2

/-- Final internal odd-local arithmetic classification:
    arithmetic multiplicative pattern <-> odd prime in exactly one base. -/
theorem T30_arithmetic_multiplicative_iff_exactly_one_base
    {a b c x y z p : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c) :
    T30ArithmeticMultiplicativePrime a b c x y z p ↔
      IsPrime p ∧ p ≠ 2 ∧ T28ExactlyOneBaseSupport p a b c := by
  rw [← T30_raw_bad_iff_exactly_one_base hx hy hz hpw]
  exact (T30_raw_bad_iff_arithmetic_multiplicative hx hy hz heq hpw).symm

/-- Explicit name for the next, genuinely non-arithmetic bridge.
    This proposition is NOT proved here and is not an axiom: a future module
    must supply a theorem from an actual formal theory of integral
    Weierstrass models, minimality, reduction type, and conductor.

    Keeping it as a definition makes the boundary inspectable without
    silently importing the desired conclusion. -/
def T30OddLocalReductionBridge : Prop :=
  ∀ a b c x y z p : Nat,
    T30ArithmeticMultiplicativePrime a b c x y z p →
    True

/-- The placeholder bridge above carries no conductor claim; it is deliberately
    tautological and cannot promote Beal. It exists only as a typed boundary
    marker for the next development. -/
theorem T30_boundary_marker_inhabited :
    T30OddLocalReductionBridge := by
  intro _ _ _ _ _ _ _ _
  trivial

#print axioms MCore.T30_raw_bad_implies_arithmetic_multiplicative
#print axioms MCore.T30_raw_bad_iff_arithmetic_multiplicative
#print axioms MCore.T30_raw_bad_iff_exactly_one_base
#print axioms MCore.T30_arithmetic_multiplicative_iff_exactly_one_base
#print axioms MCore.T30_boundary_marker_inhabited

end MCore
