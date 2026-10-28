import MCore.T42

namespace MCore

/-!
T43 — STEP 5: RESIDUAL-PRIME / IRREDUCIBILITY FRONTIER

This module isolates a necessary compatibility condition for the *single
residual prime / single Frey discriminant* route. It does not claim that every
possible generalized-Fermat strategy must use such a prime.

For the raw discriminant
  16 * A^(2x) * B^(2y) * C^(2z),
a single odd residual prime ell can divide all three exponent contributions
uniformly only if ell divides x, y, and z.
-/

/-- Compatibility of one odd residual prime with all three Beal exponents. -/
def T43SingleResidualPrimeCompatible (ell x y z : Nat) : Prop :=
  IsPrime ell ∧
  2 < ell ∧
  ell ∣ x ∧
  ell ∣ y ∧
  ell ∣ z

/-- The corresponding divisibility of the three doubled exponents occurring
    in the raw Frey discriminant. -/
def T43RawDeltaExponentCompatible (ell x y z : Nat) : Prop :=
  ell ∣ 2 * x ∧
  ell ∣ 2 * y ∧
  ell ∣ 2 * z

theorem T43_single_residual_prime_controls_raw_delta_exponents
    {ell x y z : Nat}
    (h : T43SingleResidualPrimeCompatible ell x y z) :
    T43RawDeltaExponentCompatible ell x y z := by
  rcases h with ⟨_, _, hx, hy, hz⟩
  rcases hx with ⟨kx, hx⟩
  rcases hy with ⟨ky, hy⟩
  rcases hz with ⟨kz, hz⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨2 * kx, ?_⟩
    rw [hx]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · refine ⟨2 * ky, ?_⟩
    rw [hy]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · refine ⟨2 * kz, ?_⟩
    rw [hz]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The admissible exponent triple (3,4,5) has no common divisor > 2,
    hence no single odd residual prime can divide all three exponents. -/
theorem T43_no_single_residual_prime_345 :
    ¬ ∃ ell : Nat, T43SingleResidualPrimeCompatible ell 3 4 5 := by
  rintro ⟨ell, _, hell, h3, h4, _⟩
  have hle : ell ≤ 3 :=
    Nat.le_of_dvd (by decide : 0 < (3 : Nat)) h3
  have hge : 3 ≤ ell :=
    Nat.succ_le_of_lt hell
  have heq : ell = 3 :=
    Nat.le_antisymm hle hge
  subst ell
  exact (by decide : ¬ (3 : Nat) ∣ 4) h4

/-- A universal selector of one odd residual prime from the Beal exponent
    inequalities alone is impossible. -/
def T43UniversalSingleResidualPrimeRule : Prop :=
  ∀ x y z : Nat,
    2 < x →
    2 < y →
    2 < z →
    ∃ ell : Nat, T43SingleResidualPrimeCompatible ell x y z

theorem T43_universal_single_residual_prime_rule_refuted :
    ¬ T43UniversalSingleResidualPrimeRule := by
  intro h
  have h345 := h 3 4 5 (by decide) (by decide) (by decide)
  exact T43_no_single_residual_prime_345 h345

/-- Abstract residual irreducibility predicate supplied by an actual Galois
    representation implementation. The present 4.19 kernel deliberately does
    not invent that representation. -/
def T43ResidualIrreducibilityContract
    (ResidualIrreducibleAt : Nat → Prop)
    (x y z : Nat) : Prop :=
  ∀ ell : Nat,
    T43SingleResidualPrimeCompatible ell x y z →
    ResidualIrreducibleAt ell

/-- A concrete certificate for one chosen residual prime. -/
structure T43ResidualIrreducibilityCertificate
    (ResidualIrreducibleAt : Nat → Prop)
    (x y z : Nat) where
  ell : Nat
  compatible : T43SingleResidualPrimeCompatible ell x y z
  irreducible : ResidualIrreducibleAt ell

theorem T43_certificate_supplies_irreducible_residual_prime
    {ResidualIrreducibleAt : Nat → Prop}
    {x y z : Nat}
    (c : T43ResidualIrreducibilityCertificate ResidualIrreducibleAt x y z) :
    ∃ ell : Nat,
      T43SingleResidualPrimeCompatible ell x y z ∧
      ResidualIrreducibleAt ell :=
  ⟨c.ell, c.compatible, c.irreducible⟩

/-- Exact fail-closed state for Step 5 on the current single-Frey route. -/
def T43ResidualIrreducibilityState : T36GapState :=
  .openBridge

#print axioms MCore.T43_single_residual_prime_controls_raw_delta_exponents
#print axioms MCore.T43_no_single_residual_prime_345
#print axioms MCore.T43_universal_single_residual_prime_rule_refuted
#print axioms MCore.T43_certificate_supplies_irreducible_residual_prime

end MCore
