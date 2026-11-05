import MCore.T28

namespace MCore

/-- A local-prime not dividing m is coprime to m, proved only from the
    project's elementary IsPrime definition and Lean core gcd facts. -/
theorem T29_gcd_eq_one_of_prime_not_dvd
    {p m : Nat} (hp : IsPrime p) (hpm : ¬ p ∣ m) :
    Nat.gcd p m = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro c hcp hcm
  rcases hp.2 c hcp with hc1 | hcpEq
  · exact hc1
  · subst c
    exact False.elim (hpm hcm)

/-- Euclid's lemma for the project's local IsPrime predicate. -/
theorem T29_prime_dvd_mul
    {p m n : Nat} (hp : IsPrime p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n := by
  by_cases hpm : p ∣ m
  · exact Or.inl hpm
  · right
    have hg : Nat.gcd p m = 1 :=
      T29_gcd_eq_one_of_prime_not_dvd hp hpm
    have hd : p ∣ Nat.gcd p m * n :=
      (Nat.dvd_gcd_mul_iff_dvd_mul).2 h
    simpa [hg] using hd

/-- T28's previously explicit conditional is now discharged in the local kernel. -/
theorem T29_prime_product_property_proved : T28PrimeProductProperty := by
  intro p m n hp h
  exact T29_prime_dvd_mul hp h

/-- The Frey discriminant prime-support split is therefore unconditional. -/
theorem T29_frey_prime_support
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    p ∣ 16 ∨
      p ∣ (a ^ x) ^ 2 ∨
      p ∣ (b ^ y) ^ 2 ∨
      p ∣ (c ^ z) ^ 2 :=
  T28_frey_prime_support_of_product_property
    T29_prime_product_property_proved hp hDelta

#print axioms MCore.T29_gcd_eq_one_of_prime_not_dvd
#print axioms MCore.T29_prime_dvd_mul
#print axioms MCore.T29_prime_product_property_proved
#print axioms MCore.T29_frey_prime_support

end MCore
