import MCore.T7

namespace MCore

/-- Exact elementary kernel needed to reflect a prime divisor through a power. -/
def T8PrimePowerReflection : Prop :=
  ∀ p a k : Nat, IsPrime p → p ∣ a ^ k → p ∣ a

/-- Euclid's lemma, isolated for the project's local divisor-only prime notion. -/
def T8EuclidKernel : Prop :=
  ∀ p a b : Nat, IsPrime p → p ∣ a * b → p ∣ a ∨ p ∣ b

/-- Once prime divisors reflect through powers, primitiveness is preserved when
    the three bases are independently replaced by powers. -/
theorem T8_powered_primitive
    (hReflect : T8PrimePowerReflection)
    {a b c ka kb kc : Nat}
    (hPrimitive : ¬ ∃ q : Nat, CommonDivisor q a b c) :
    ¬ ∃ q : Nat, CommonDivisor q (a ^ ka) (b ^ kb) (c ^ kc) := by
  intro hPowered
  rcases hPowered with ⟨q, hqgt, hqa, hqb, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpaPow : p ∣ a ^ ka := nat_dvd_trans hpq hqa
  have hpbPow : p ∣ b ^ kb := nat_dvd_trans hpq hqb
  have hpcPow : p ∣ c ^ kc := nat_dvd_trans hpq hqc
  have hpa : p ∣ a := hReflect p a ka hp hpaPow
  have hpb : p ∣ b := hReflect p b kb hp hpbPow
  have hpc : p ∣ c := hReflect p c kc hp hpcPow
  exact hPrimitive ⟨p, hp.1, hpa, hpb, hpc⟩

/-- The remaining T8 bridge after the powered-primitivity transport is isolated:
    prove prime-power reflection for the local notion of prime. -/
theorem T8_transport_reduces_to_reflection
    (h : T8PrimePowerReflection)
    {a b c ka kb kc : Nat}
    (hPrimitive : ¬ ∃ q : Nat, CommonDivisor q a b c) :
    ¬ ∃ q : Nat, CommonDivisor q (a ^ ka) (b ^ kb) (c ^ kc) :=
  T8_powered_primitive h hPrimitive

#print axioms MCore.T8_powered_primitive
#print axioms MCore.T8_transport_reduces_to_reflection

end MCore
