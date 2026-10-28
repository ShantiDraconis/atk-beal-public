import MCore.T45

namespace MCore

/-!
T48 — STRUCTURAL CLASSIFICATION OF MIXED REDUCED SIGNATURES

Once T7 has reduced every exponent to either 4 or a prime, and T45 has
removed the equal odd-prime branch, every remaining signature belongs to one
of three structural families:

1. at least one exponent is 4;
2. all three exponents are prime and exactly two are equal;
3. all three exponents are prime and pairwise distinct.

These are the three signature families that a complete mixed Beal
Frey/newform elimination must cover.
-/

def T48ContainsFour (x y z : Nat) : Prop :=
  x = 4 ∨ y = 4 ∨ z = 4

def T48AllPrime (x y z : Nat) : Prop :=
  IsPrime x ∧ IsPrime y ∧ IsPrime z

def T48ExactlyTwoEqual (x y z : Nat) : Prop :=
  (x = y ∧ x ≠ z) ∨
  (x = z ∧ x ≠ y) ∨
  (y = z ∧ y ≠ x)

def T48AllDistinct (x y z : Nat) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- A T7-reduced signature either contains a 4 or consists of three primes. -/
theorem T48_reduced_four_or_all_prime
    {x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z) :
    T48ContainsFour x y z ∨ T48AllPrime x y z := by
  rcases hx.2 with hx4 | hxp
  · exact Or.inl (Or.inl hx4)
  · rcases hy.2 with hy4 | hyp
    · exact Or.inl (Or.inr (Or.inl hy4))
    · rcases hz.2 with hz4 | hzp
      · exact Or.inl (Or.inr (Or.inr hz4))
      · exact Or.inr ⟨hxp, hyp, hzp⟩

/-- If a mixed reduced signature has no 4, then all three exponents are prime
    and they are not all equal. -/
theorem T48_mixed_coarse_split
    {x y z : Nat}
    (h : T45MixedReducedSignature x y z) :
    T48ContainsFour x y z ∨
      (T48AllPrime x y z ∧ ¬ (x = y ∧ y = z)) := by
  rcases T48_reduced_four_or_all_prime h.1 h.2.1 h.2.2.1 with h4 | hp
  · exact Or.inl h4
  · right
    refine ⟨hp, ?_⟩
    intro hall
    apply h.2.2.2
    rcases hall with ⟨hxy, hyz⟩
    have hyx : y = x := hxy.symm
    have hzx : z = x := (hxy.trans hyz).symm
    exact ⟨x, hp.1, h.1.1, rfl, hyx, hzx⟩

/-- Pure equality trichotomy after excluding the all-equal case. -/
theorem T48_not_all_equal_split
    {x y z : Nat}
    (hnot : ¬ (x = y ∧ y = z)) :
    T48ExactlyTwoEqual x y z ∨ T48AllDistinct x y z := by
  by_cases hxy : x = y
  · left
    left
    refine ⟨hxy, ?_⟩
    intro hxz
    apply hnot
    exact ⟨hxy, hxy.symm.trans hxz⟩
  · by_cases hxz : x = z
    · left
      right
      left
      exact ⟨hxz, hxy⟩
    · by_cases hyz : y = z
      · left
        right
        right
        refine ⟨hyz, ?_⟩
        intro hyx
        exact hxy hyx.symm
      · right
        exact ⟨hxy, hxz, hyz⟩

/-- Final three-family classification of every mixed reduced signature. -/
theorem T48_mixed_signature_three_family_split
    {x y z : Nat}
    (h : T45MixedReducedSignature x y z) :
    T48ContainsFour x y z ∨
      (T48AllPrime x y z ∧ T48ExactlyTwoEqual x y z) ∨
      (T48AllPrime x y z ∧ T48AllDistinct x y z) := by
  rcases T48_mixed_coarse_split h with h4 | hprime
  · exact Or.inl h4
  · rcases T48_not_all_equal_split hprime.2 with htwo | hdistinct
    · exact Or.inr (Or.inl ⟨hprime.1, htwo⟩)
    · exact Or.inr (Or.inr ⟨hprime.1, hdistinct⟩)

/-- The three mixed-signature families that Step 8 must eliminate. -/
inductive T48MixedFamily
  | containsFour
  | twoEqualPrimes
  | threeDistinctPrimes

/-- Fail-closed statement of the remaining Step-8 mixed family obligations. -/
structure T48MixedFamilyEliminationLedger where
  containsFourEliminated : Prop
  twoEqualPrimesEliminated : Prop
  threeDistinctPrimesEliminated : Prop

def T48AllMixedFamiliesEliminated
    (L : T48MixedFamilyEliminationLedger) : Prop :=
  L.containsFourEliminated ∧
  L.twoEqualPrimesEliminated ∧
  L.threeDistinctPrimesEliminated

#print axioms MCore.T48_reduced_four_or_all_prime
#print axioms MCore.T48_mixed_coarse_split
#print axioms MCore.T48_not_all_equal_split
#print axioms MCore.T48_mixed_signature_three_family_split

end MCore
