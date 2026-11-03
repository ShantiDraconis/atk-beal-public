import MCore.T44

namespace MCore

/-!
T45 — CLASSIFICATION OF THE SINGLE-RESIDUAL-PRIME ROUTE

After T7 every reduced exponent is either 4 or prime. Therefore one odd prime
ell dividing all three reduced exponents can occur only when all three
exponents are exactly ell. This identifies the single-ell route with the
equal-prime (FLT-type) signature branch.
-/

/-- No odd local prime can divide 4. -/
theorem T45_odd_prime_not_dvd_four
    {ell : Nat}
    (hellPrime : IsPrime ell)
    (hellOdd : 2 < ell) :
    ¬ ell ∣ 4 := by
  intro h4
  have h22 : ell ∣ 2 * 2 := by
    simpa using h4
  rcases T29_prime_dvd_mul hellPrime h22 with h2 | h2
  · have hle : ell ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < (2 : Nat)) h2
    exact (Nat.not_lt_of_ge hle) hellOdd
  · have hle : ell ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < (2 : Nat)) h2
    exact (Nat.not_lt_of_ge hle) hellOdd

/-- If a reduced exponent is divisible by an odd local prime, then the
    exponent itself is that prime. -/
theorem T45_reduced_exponent_eq_residual_prime
    {ell r : Nat}
    (hellPrime : IsPrime ell)
    (hellOdd : 2 < ell)
    (hr : T7ReducedExponent r)
    (hdiv : ell ∣ r) :
    r = ell := by
  rcases hr.2 with h4 | hrPrime
  · subst r
    exact False.elim (T45_odd_prime_not_dvd_four hellPrime hellOdd hdiv)
  · rcases hrPrime.2 ell hdiv with h1 | heq
    · subst ell
      exact False.elim ((by decide : ¬ (2 < (1 : Nat))) hellOdd)
    · exact heq.symm

/-- Equal odd-prime signature. -/
def T45EqualOddPrimeSignature (x y z : Nat) : Prop :=
  ∃ ell : Nat,
    IsPrime ell ∧
    2 < ell ∧
    x = ell ∧
    y = ell ∧
    z = ell

theorem T45_single_residual_prime_for_reduced_signature_is_equal
    {ell x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (h : T43SingleResidualPrimeCompatible ell x y z) :
    x = ell ∧ y = ell ∧ z = ell := by
  rcases h with ⟨hellPrime, hellOdd, hdx, hdy, hdz⟩
  exact ⟨
    T45_reduced_exponent_eq_residual_prime hellPrime hellOdd hx hdx,
    T45_reduced_exponent_eq_residual_prime hellPrime hellOdd hy hdy,
    T45_reduced_exponent_eq_residual_prime hellPrime hellOdd hz hdz
  ⟩

theorem T45_equal_signature_supplies_single_residual_prime
    {x y z : Nat}
    (h : T45EqualOddPrimeSignature x y z) :
    ∃ ell : Nat, T43SingleResidualPrimeCompatible ell x y z := by
  rcases h with ⟨ell, hp, h2, hx, hy, hz⟩
  subst x
  subst y
  subst z
  have hd : ell ∣ ell := ⟨1, (Nat.mul_one ell).symm⟩
  exact ⟨ell, hp, h2, hd, hd, hd⟩

/-- Exact classification: on T7-reduced signatures, the single-ell route is
    available iff the signature is equal odd-prime. -/
theorem T45_single_residual_prime_iff_equal_prime_signature
    {x y z : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z) :
    (∃ ell : Nat, T43SingleResidualPrimeCompatible ell x y z) ↔
      T45EqualOddPrimeSignature x y z := by
  constructor
  · rintro ⟨ell, hcompat⟩
    have heq :=
      T45_single_residual_prime_for_reduced_signature_is_equal
        hx hy hz hcompat
    exact ⟨ell, hcompat.1, hcompat.2.1, heq.1, heq.2.1, heq.2.2⟩
  · exact T45_equal_signature_supplies_single_residual_prime

/-- Mixed T7-reduced signatures cannot use the one-residual-prime route. -/
def T45MixedReducedSignature (x y z : Nat) : Prop :=
  T7ReducedExponent x ∧
  T7ReducedExponent y ∧
  T7ReducedExponent z ∧
  ¬ T45EqualOddPrimeSignature x y z

theorem T45_mixed_signature_has_no_single_residual_prime
    {x y z : Nat}
    (h : T45MixedReducedSignature x y z) :
    ¬ ∃ ell : Nat, T43SingleResidualPrimeCompatible ell x y z := by
  intro hres
  apply h.2.2.2
  exact (T45_single_residual_prime_iff_equal_prime_signature
    h.1 h.2.1 h.2.2.1).mp hres

/-- Scientific split for Step 5:
    equal odd-prime signatures may enter the classical FLT single-ell route;
    every mixed reduced signature requires a different signature-specific
    Frey/residual construction. -/
inductive T45ResidualRoute
  | equalPrimeFLT
  | mixedSignatureSpecific

noncomputable def T45ResidualRouteFor (x y z : Nat) : T45ResidualRoute := by
  classical
  exact if _h : T45EqualOddPrimeSignature x y z
    then .equalPrimeFLT
    else .mixedSignatureSpecific

#print axioms MCore.T45_odd_prime_not_dvd_four
#print axioms MCore.T45_reduced_exponent_eq_residual_prime
#print axioms MCore.T45_single_residual_prime_for_reduced_signature_is_equal
#print axioms MCore.T45_single_residual_prime_iff_equal_prime_signature
#print axioms MCore.T45_mixed_signature_has_no_single_residual_prime

end MCore
