import MCore.T45

namespace MCore

/-!
T47 — EQUAL-PRIME BRANCH REDUCES TO FLT

T45 proves that the current single-residual-prime route can occur, after T7
reduction, only when x = y = z = ell for one odd prime ell. Therefore the
Beal equation on that branch is literally a Fermat equation of exponent ell.
-/

/-- External mathematical content needed to close one FLT exponent. -/
def T47FLTAt (ell : Nat) : Prop :=
  ∀ a b c : Nat,
    0 < a →
    0 < b →
    0 < c →
    a ^ ell + b ^ ell = c ^ ell →
    False

/-- The reduced single-residual-prime Beal equation is exactly an FLT
    equation at that residual prime. -/
theorem T47_beal_equation_to_flt_equation
    {a b c x y z ell : Nat}
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (hcompat : T43SingleResidualPrimeCompatible ell x y z)
    (heq : a ^ x + b ^ y = c ^ z) :
    a ^ ell + b ^ ell = c ^ ell := by
  have hs :=
    T45_single_residual_prime_for_reduced_signature_is_equal
      hx hy hz hcompat
  rw [hs.1, hs.2.1, hs.2.2] at heq
  exact heq

/-- Any certified FLT theorem at ell eliminates the corresponding
    equal-prime Beal branch. -/
theorem T47_flt_eliminates_single_residual_branch
    {a b c x y z ell : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (hcompat : T43SingleResidualPrimeCompatible ell x y z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hFLT : T47FLTAt ell) :
    False := by
  exact hFLT a b c ha hb hc
    (T47_beal_equation_to_flt_equation hx hy hz hcompat heq)

/-- A family-level FLT certificate adequate for every equal-prime reduced
    signature relevant to T45. -/
structure T47FLTFamilyCertificate where
  closes :
    ∀ ell : Nat,
      IsPrime ell →
      2 < ell →
      T47FLTAt ell

theorem T47_family_certificate_eliminates_equal_prime_signature
    {a b c x y z : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : T7ReducedExponent x)
    (hy : T7ReducedExponent y)
    (hz : T7ReducedExponent z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hEqual : T45EqualOddPrimeSignature x y z)
    (cert : T47FLTFamilyCertificate) :
    False := by
  rcases hEqual with ⟨ell, hp, h2, hxe, hye, hze⟩
  subst x
  subst y
  subst z
  exact cert.closes ell hp h2 a b c ha hb hc heq

/-- Scientific state: the reduction to FLT is certified here; the actual FLT
    family theorem must be imported/proved separately before this branch may
    be marked closed in the final Beal bundle. -/
def T47EqualPrimeFLTState : T36GapState :=
  .openBridge

#print axioms MCore.T47_beal_equation_to_flt_equation
#print axioms MCore.T47_flt_eliminates_single_residual_branch
#print axioms MCore.T47_family_certificate_eliminates_equal_prime_signature

end MCore
