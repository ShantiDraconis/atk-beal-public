import MCore.T28

namespace MCore

/-- c4 for the integral Frey model
      Y^2 = X (X - A^x) (X + B^y)
    written with u=A^x and v=B^y:
      c4 = 16 (u^2 + uv + v^2).

    T29 uses this only as exact integer arithmetic. No reduction-type theorem
    is imported or assumed here. -/
def T29FreyC4 (a b x y : Nat) : Nat :=
  16 * ((a ^ x) ^ 2 + (a ^ x) * (b ^ y) + (b ^ y) ^ 2)

theorem T29_odd_prime_not_dvd_sixteen
    {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) :
    ¬ p ∣ 16 := by
  intro h16
  exact hp2 (T27_prime_dvd_sixteen_eq_two hp h16)

/-- If p divides A but not B, then the odd prime p cannot divide c4. -/
theorem T29_frey_c4_not_dvd_of_a_support
    {a b x y p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hx : 0 < x)
    (hpa : p ∣ a)
    (hpb : ¬ p ∣ b) :
    ¬ p ∣ T29FreyC4 a b x y := by
  intro hc4
  unfold T29FreyC4 at hc4
  rcases T27_prime_dvd_mul hp hc4 with h16 | hinner
  · exact T29_odd_prime_not_dvd_sixteen hp hp2 h16
  · have hax : p ∣ a ^ x :=
      T11_dvd_pow_of_dvd hx hpa
    have ha2 : p ∣ (a ^ x) ^ 2 :=
      T11_dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hax
    have hab : p ∣ (a ^ x) * (b ^ y) :=
      Nat.dvd_mul_right_of_dvd hax (b ^ y)
    have hfirst : p ∣ (a ^ x) ^ 2 + (a ^ x) * (b ^ y) :=
      T11_dvd_add ha2 hab
    have hb2 : p ∣ (b ^ y) ^ 2 :=
      (Nat.dvd_add_iff_right hfirst).2 hinner
    have hby : p ∣ b ^ y :=
      T27_prime_dvd_pow hp hb2
    exact hpb (T27_prime_dvd_pow hp hby)

/-- Symmetric B-support case. -/
theorem T29_frey_c4_not_dvd_of_b_support
    {a b x y p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hy : 0 < y)
    (hpa : ¬ p ∣ a)
    (hpb : p ∣ b) :
    ¬ p ∣ T29FreyC4 a b x y := by
  intro hc4
  unfold T29FreyC4 at hc4
  rcases T27_prime_dvd_mul hp hc4 with h16 | hinner
  · exact T29_odd_prime_not_dvd_sixteen hp hp2 h16
  · have hby : p ∣ b ^ y :=
      T11_dvd_pow_of_dvd hy hpb
    have hab : p ∣ (a ^ x) * (b ^ y) :=
      Nat.dvd_mul_left_of_dvd hby (a ^ x)
    have hb2 : p ∣ (b ^ y) ^ 2 :=
      T11_dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) hby
    have htail : p ∣ (a ^ x) * (b ^ y) + (b ^ y) ^ 2 :=
      T11_dvd_add hab hb2
    have hinner' :
        p ∣ (a ^ x) ^ 2 + ((a ^ x) * (b ^ y) + (b ^ y) ^ 2) := by
      simpa [Nat.add_assoc] using hinner
    have ha2 : p ∣ (a ^ x) ^ 2 :=
      (Nat.dvd_add_iff_left htail).2 hinner'
    have hax : p ∣ a ^ x :=
      T27_prime_dvd_pow hp ha2
    exact hpa (T27_prime_dvd_pow hp hax)

/-- C-support case. The Beal equation gives p | (A^x+B^y); together with
    p | c4 this would force p | B, contradicting pairwise-primitiveness. -/
theorem T29_frey_c4_not_dvd_of_c_support
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpc : p ∣ c)
    (hpb : ¬ p ∣ b) :
    ¬ p ∣ T29FreyC4 a b x y := by
  intro hc4
  unfold T29FreyC4 at hc4
  rcases T27_prime_dvd_mul hp hc4 with h16 | hinner
  · exact T29_odd_prime_not_dvd_sixteen hp hp2 h16
  · have hcz : p ∣ c ^ z :=
      T11_dvd_pow_of_dvd hz hpc
    have hsum : p ∣ a ^ x + b ^ y := by
      rw [heq]
      exact hcz
    have hterm : p ∣ (a ^ x) * (a ^ x + b ^ y) :=
      Nat.dvd_mul_left_of_dvd hsum (a ^ x)
    have hinner' :
        p ∣ (a ^ x) * (a ^ x + b ^ y) + (b ^ y) ^ 2 := by
      simpa [Nat.mul_add, Nat.pow_succ, Nat.add_assoc] using hinner
    have hb2 : p ∣ (b ^ y) ^ 2 :=
      (Nat.dvd_add_iff_right hterm).2 hinner'
    have hby : p ∣ b ^ y :=
      T27_prime_dvd_pow hp hb2
    exact hpb (T27_prime_dvd_pow hp hby)

/-- Arithmetic precursor to odd multiplicative reduction:
    for a pairwise-primitive Beal/Frey candidate, every odd prime in the
    discriminant support is absent from c4. -/
theorem T29_frey_odd_support_not_c4
    {a b c x y z p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpw : T11PairwisePrimitive a b c)
    (hDelta : p ∣ T24FreyDiscriminantBeal a b c x y z) :
    ¬ p ∣ T29FreyC4 a b x y := by
  have hexact :=
    T28_frey_odd_prime_exactly_one_base hp hp2 hx hy hz hpw hDelta
  rcases hexact with ha | hb | hc
  · exact T29_frey_c4_not_dvd_of_a_support hp hp2 hx ha.1 ha.2.1
  · exact T29_frey_c4_not_dvd_of_b_support hp hp2 hy hb.1 hb.2.1
  · exact T29_frey_c4_not_dvd_of_c_support hp hp2 hz heq hc.2.2 hc.2.1

#print axioms MCore.T29_frey_c4_not_dvd_of_a_support
#print axioms MCore.T29_frey_c4_not_dvd_of_b_support
#print axioms MCore.T29_frey_c4_not_dvd_of_c_support
#print axioms MCore.T29_frey_odd_support_not_c4

end MCore
