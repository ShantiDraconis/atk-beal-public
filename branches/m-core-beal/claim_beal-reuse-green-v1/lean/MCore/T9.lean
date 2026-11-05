import Init.Data.Nat.Gcd
import MCore.T8

namespace MCore

/-- T9 closes Euclid's lemma for the project's local prime notion using the
    core Nat.dvd_mul factorization theorem. No external package is required. -/
theorem T9_euclidKernel_proved : T8EuclidKernel := by
  intro p a b hp hpab
  rcases (Nat.dvd_mul.mp hpab) with ⟨p₁, p₂, hp₁a, hp₂b, hprod⟩
  have hp₁p : p₁ ∣ p := ⟨p₂, hprod.symm⟩
  rcases hp.2 p₁ hp₁p with hp₁one | hp₁eq
  · subst p₁
    have hp₂eq : p₂ = p := by
      simpa using hprod
    subst p₂
    exact Or.inr hp₂b
  · subst p₁
    exact Or.inl hp₁a

private theorem T9_prime_not_dvd_one
    {p : Nat} (hp : IsPrime p) : ¬ p ∣ 1 := by
  intro h
  rcases h with ⟨m, hm⟩
  cases m with
  | zero =>
      have h10 : (1 : Nat) = 0 := by simpa using hm
      exact Nat.one_ne_zero h10
  | succ m =>
      have hple : p ≤ 1 := by
        rw [hm]
        exact Nat.le_mul_of_pos_right p (Nat.zero_lt_succ m)
      exact (Nat.not_le_of_gt hp.1) hple

/-- Euclid's lemma implies reflection of a prime divisor through every power. -/
theorem T9_primePowerReflection_of_euclid
    (hE : T8EuclidKernel) : T8PrimePowerReflection := by
  intro p a k hp hdiv
  induction k with
  | zero =>
      have hpone : p ∣ 1 := by simpa using hdiv
      exact False.elim (T9_prime_not_dvd_one hp hpone)
  | succ k ih =>
      have hmul : p ∣ a ^ k * a := by
        simpa [Nat.pow_succ] using hdiv
      rcases hE p (a ^ k) a hp hmul with hprev | ha
      · exact ih hprev
      · exact ha

theorem T9_primePowerReflection_proved : T8PrimePowerReflection :=
  T9_primePowerReflection_of_euclid T9_euclidKernel_proved

/-- T9 discharges the conditional hypothesis of T8. -/
theorem T9_powered_primitive_unconditional
    {a b c ka kb kc : Nat}
    (hPrimitive : ¬ ∃ q : Nat, CommonDivisor q a b c) :
    ¬ ∃ q : Nat, CommonDivisor q (a ^ ka) (b ^ kb) (c ^ kc) :=
  T8_powered_primitive T9_primePowerReflection_proved hPrimitive

#print axioms MCore.T9_euclidKernel_proved
#print axioms MCore.T9_primePowerReflection_proved
#print axioms MCore.T9_powered_primitive_unconditional

end MCore
