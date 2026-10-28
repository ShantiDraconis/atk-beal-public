import MCore.T12

namespace MCore

/--
Primitive local-support law: under pairwise primitiveness, any nontrivial
divisor of a cannot divide b.
-/
theorem T61_divisor_of_a_not_divide_b
    {q a b c : Nat}
    (hq : 1 < q)
    (hpw : T11PairwisePrimitive a b c)
    (hqa : q ∣ a) :
    ¬ q ∣ b := by
  intro hqb
  exact hpw.1 ⟨q, hq, hqa, hqb⟩

/-- Symmetric a/c local-support exclusion. -/
theorem T61_divisor_of_a_not_divide_c
    {q a b c : Nat}
    (hq : 1 < q)
    (hpw : T11PairwisePrimitive a b c)
    (hqa : q ∣ a) :
    ¬ q ∣ c := by
  intro hqc
  exact hpw.2.1 ⟨q, hq, hqa, hqc⟩

/-- Symmetric b/c local-support exclusion. -/
theorem T61_divisor_of_b_not_divide_c
    {q a b c : Nat}
    (hq : 1 < q)
    (hpw : T11PairwisePrimitive a b c)
    (hqb : q ∣ b) :
    ¬ q ∣ c := by
  intro hqc
  exact hpw.2.2 ⟨q, hq, hqb, hqc⟩

/-- If a nontrivial divisor lies in c, it lies in neither a nor b. -/
theorem T61_divisor_of_c_is_disjoint_from_ab
    {q a b c : Nat}
    (hq : 1 < q)
    (hpw : T11PairwisePrimitive a b c)
    (hqc : q ∣ c) :
    ¬ q ∣ a ∧ ¬ q ∣ b := by
  constructor
  · intro hqa
    exact hpw.2.1 ⟨q, hq, hqa, hqc⟩
  · intro hqb
    exact hpw.2.2 ⟨q, hq, hqb, hqc⟩

/--
If q divides a in a primitive Beal equation, then q divides a^x but divides
neither b nor c.  This is exactly the local support separation used by any
Frey discriminant/conductor calculation.
-/
theorem T61_local_support_a
    {q a b c x y z : Nat}
    (hq : 1 < q)
    (hx : 0 < x)
    (hpw : T11PairwisePrimitive a b c)
    (hqa : q ∣ a) :
    q ∣ a ^ x ∧ ¬ q ∣ b ∧ ¬ q ∣ c := by
  refine ⟨T11_dvd_pow_of_dvd hx hqa, ?_, ?_⟩
  · exact T61_divisor_of_a_not_divide_b hq hpw hqa
  · exact T61_divisor_of_a_not_divide_c hq hpw hqa

/-- Corresponding local support law for b. -/
theorem T61_local_support_b
    {q a b c x y z : Nat}
    (hq : 1 < q)
    (hy : 0 < y)
    (hpw : T11PairwisePrimitive a b c)
    (hqb : q ∣ b) :
    ¬ q ∣ a ∧ q ∣ b ^ y ∧ ¬ q ∣ c := by
  refine ⟨?_, T11_dvd_pow_of_dvd hy hqb, ?_⟩
  · intro hqa
    exact hpw.1 ⟨q, hq, hqa, hqb⟩
  · exact T61_divisor_of_b_not_divide_c hq hpw hqb

/-- Corresponding local support law for c. -/
theorem T61_local_support_c
    {q a b c x y z : Nat}
    (hq : 1 < q)
    (hz : 0 < z)
    (hpw : T11PairwisePrimitive a b c)
    (hqc : q ∣ c) :
    ¬ q ∣ a ∧ ¬ q ∣ b ∧ q ∣ c ^ z := by
  rcases T61_divisor_of_c_is_disjoint_from_ab hq hpw hqc with ⟨ha,hb⟩
  exact ⟨ha, hb, T11_dvd_pow_of_dvd hz hqc⟩

/--
Exactly-one-even plus pairwise primitiveness gives a unique local support for
the prime 2.  This packages the parity information in the same support language
used for odd primes.
-/
theorem T61_two_has_unique_base_support
    {a b c : Nat}
    (hpar : T12ExactlyOneEven a b c) :
    (2 ∣ a ∧ ¬ 2 ∣ b ∧ ¬ 2 ∣ c) ∨
    (¬ 2 ∣ a ∧ 2 ∣ b ∧ ¬ 2 ∣ c) ∨
    (¬ 2 ∣ a ∧ ¬ 2 ∣ b ∧ 2 ∣ c) := by
  exact hpar

#print axioms MCore.T61_divisor_of_a_not_divide_b
#print axioms MCore.T61_divisor_of_c_is_disjoint_from_ab
#print axioms MCore.T61_local_support_a
#print axioms MCore.T61_local_support_b
#print axioms MCore.T61_local_support_c
#print axioms MCore.T61_two_has_unique_base_support

end MCore
