import MCore.T49

namespace MCore

/-!
T51 — FIVE RESIDUAL MIXED SIGNATURE FAMILIES

After T7 reduction and after removing the all-four FLT(4) branch, every mixed
signature belongs to one of five structural families:

1. (4,4,p) up to permutation, p an odd prime;
2. (4,p,p) up to permutation, p an odd prime;
3. (4,p,q) up to permutation, p,q distinct odd primes;
4. (p,p,q) up to permutation, p,q distinct odd primes;
5. (p,q,r) pairwise distinct odd primes.

This is a finite classification of signature *types*, not a finite list of
numerical signatures.
-/

def T51OddPrimeExponent (p : Nat) : Prop :=
  IsPrime p ∧ 2 < p

theorem T51_prime_of_reduced_ne_four
    {r : Nat}
    (hr : T7ReducedExponent r)
    (hne : r ≠ 4) :
    T51OddPrimeExponent r := by
  exact ⟨hr.2.resolve_left hne, hr.1⟩

def T51TwoFourPrime (x y z : Nat) : Prop :=
  (x = 4 ∧ y = 4 ∧ T51OddPrimeExponent z) ∨
  (x = 4 ∧ z = 4 ∧ T51OddPrimeExponent y) ∨
  (y = 4 ∧ z = 4 ∧ T51OddPrimeExponent x)

def T51OneFourEqualPrimes (x y z : Nat) : Prop :=
  (x = 4 ∧ T51OddPrimeExponent y ∧ z = y) ∨
  (y = 4 ∧ T51OddPrimeExponent x ∧ z = x) ∨
  (z = 4 ∧ T51OddPrimeExponent x ∧ y = x)

def T51OneFourDistinctPrimes (x y z : Nat) : Prop :=
  (x = 4 ∧ T51OddPrimeExponent y ∧ T51OddPrimeExponent z ∧ y ≠ z) ∨
  (y = 4 ∧ T51OddPrimeExponent x ∧ T51OddPrimeExponent z ∧ x ≠ z) ∨
  (z = 4 ∧ T51OddPrimeExponent x ∧ T51OddPrimeExponent y ∧ x ≠ y)

theorem T51_exactly_two_four_to_prime_family
    {x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (h : T49ExactlyTwoFour x y z) :
    T51TwoFourPrime x y z := by
  rcases h with hxy | hxz | hyz
  · exact Or.inl ⟨hxy.1, hxy.2.1,
      T51_prime_of_reduced_ne_four hz hxy.2.2⟩
  · exact Or.inr (Or.inl ⟨hxz.1, hxz.2.1,
      T51_prime_of_reduced_ne_four hy hxz.2.2⟩)
  · exact Or.inr (Or.inr ⟨hyz.1, hyz.2.1,
      T51_prime_of_reduced_ne_four hx hyz.2.2⟩)

theorem T51_exactly_one_four_split
    {x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (h : T49ExactlyOneFour x y z) :
    T51OneFourEqualPrimes x y z ∨
      T51OneFourDistinctPrimes x y z := by
  rcases h with hx4 | hy4 | hz4
  ·
    have hyp := T51_prime_of_reduced_ne_four hy hx4.2.1
    have hzp := T51_prime_of_reduced_ne_four hz hx4.2.2
    by_cases hyz : y = z
    · left
      exact Or.inl ⟨hx4.1, hyp, hyz.symm⟩
    · right
      exact Or.inl ⟨hx4.1, hyp, hzp, hyz⟩
  ·
    have hxp := T51_prime_of_reduced_ne_four hx hy4.2.1
    have hzp := T51_prime_of_reduced_ne_four hz hy4.2.2
    by_cases hxz : x = z
    · left
      exact Or.inr (Or.inl ⟨hy4.1, hxp, hxz.symm⟩)
    · right
      exact Or.inr (Or.inl ⟨hy4.1, hxp, hzp, hxz⟩)
  ·
    have hxp := T51_prime_of_reduced_ne_four hx hz4.2.1
    have hyp := T51_prime_of_reduced_ne_four hy hz4.2.2
    by_cases hxy : x = y
    · left
      exact Or.inr (Or.inr ⟨hz4.1, hxp, hxy.symm⟩)
    · right
      exact Or.inr (Or.inr ⟨hz4.1, hxp, hyp, hxy⟩)

def T51MixedFiveFamilySplit (x y z : Nat) : Prop :=
  T51TwoFourPrime x y z ∨
  T51OneFourEqualPrimes x y z ∨
  T51OneFourDistinctPrimes x y z ∨
  (T48AllPrime x y z ∧ T48ExactlyTwoEqual x y z) ∨
  (T48AllPrime x y z ∧ T48AllDistinct x y z)

/-- Complete five-family classification after excluding all-four. -/
theorem T51_mixed_reduced_five_family_split
    {x y z : Nat}
    (hMixed : T45MixedReducedSignature x y z)
    (hNotAllFour : ¬ T49AllFour x y z) :
    T51MixedFiveFamilySplit x y z := by
  rcases T48_mixed_signature_three_family_split hMixed with h4 | hTwoPrime | hDistinctPrime
  ·
    rcases T49_contains_four_trichotomy h4 with hAll | hTwo4 | hOne4
    · exact False.elim (hNotAllFour hAll)
    · exact Or.inl
        (T51_exactly_two_four_to_prime_family
          hMixed.1 hMixed.2.1 hMixed.2.2.1 hTwo4)
    ·
      rcases T51_exactly_one_four_split
        hMixed.1 hMixed.2.1 hMixed.2.2.1 hOne4 with hEq | hNe
      · exact Or.inr (Or.inl hEq)
      · exact Or.inr (Or.inr (Or.inl hNe))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hTwoPrime)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hDistinctPrime)))

/-- The five signature families requiring signature-specific residual/newform
    analysis after the small FLT branches are removed. -/
inductive T51MixedSignatureFamily
  | twoFourPrime
  | oneFourEqualPrimes
  | oneFourDistinctPrimes
  | twoEqualOddPrimes
  | threeDistinctOddPrimes

#print axioms MCore.T51_prime_of_reduced_ne_four
#print axioms MCore.T51_exactly_two_four_to_prime_family
#print axioms MCore.T51_exactly_one_four_split
#print axioms MCore.T51_mixed_reduced_five_family_split

end MCore
