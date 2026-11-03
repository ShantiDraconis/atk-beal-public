import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

/-- Recursive quotient: b^n + (c-b)Q_n(c,b) = c^n when b ≤ c. -/
def CoreDiffQuot (c b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c ^ n + b * CoreDiffQuot c b n

theorem core_diff_factorization
    {b c : Nat}
    (hbc : b ≤ c) :
    ∀ n : Nat, b ^ n + (c - b) * CoreDiffQuot c b n = c ^ n := by
  intro n
  induction n with
  | zero =>
      simp [CoreDiffQuot]
  | succ n ih =>
      change b ^ (n + 1) + (c - b) * (c ^ n + b * CoreDiffQuot c b n) =
        c ^ (n + 1)
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        b ^ n * b + (c - b) * (c ^ n + b * CoreDiffQuot c b n)
            = b * (b ^ n + (c - b) * CoreDiffQuot c b n) +
                (c - b) * c ^ n := by
                simp [Nat.left_distrib, Nat.right_distrib, Nat.mul_assoc,
                  Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]
        _ = b * c ^ n + (c - b) * c ^ n := by rw [ih]
        _ = (b + (c - b)) * c ^ n := by rw [Nat.add_mul]
        _ = c * c ^ n := by rw [Nat.add_comm b, Nat.sub_add_cancel hbc]
        _ = c ^ n * c := Nat.mul_comm _ _

theorem core_right_same_exponent_gap
    {a b c x n : Nat}
    (ha : 0 < a)
    (heq : a ^ x + b ^ n = c ^ n) :
    b < c := by
  have hax : 0 < a ^ x := Nat.pow_pos ha
  have hp : b ^ n < c ^ n := by
    rw [← heq]
    exact Nat.lt_add_of_pos_left hax
  match Nat.lt_or_ge b c with
  | Or.inl h => exact h
  | Or.inr h =>
      have hpow : c ^ n ≤ b ^ n := Nat.pow_le_pow_left h n
      exact False.elim ((Nat.not_le_of_gt hp) hpow)

theorem reduced_y_eq_z_exact_factor
    (r : ReducedPrimitiveCandidate)
    (hyz : r.y = r.z) :
    r.a ^ r.x = (r.c - r.b) * CoreDiffQuot r.c r.b r.y := by
  have hbc_lt : r.b < r.c := by
    apply core_right_same_exponent_gap r.a_pos
    simpa [hyz] using r.equation
  have hbc : r.b ≤ r.c := Nat.le_of_lt hbc_lt
  have hfac := core_diff_factorization hbc r.y
  have hleft : r.b ^ r.y + r.a ^ r.x = r.c ^ r.y := by
    simpa [Nat.add_comm, hyz] using r.equation
  have hsum :
      r.b ^ r.y + r.a ^ r.x =
        r.b ^ r.y + (r.c - r.b) * CoreDiffQuot r.c r.b r.y :=
    hleft.trans hfac.symm
  exact Nat.add_left_cancel hsum

theorem reduced_x_eq_z_exact_factor
    (r : ReducedPrimitiveCandidate)
    (hxz : r.x = r.z) :
    r.b ^ r.y = (r.c - r.a) * CoreDiffQuot r.c r.a r.x := by
  have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.x := by
    simpa [Nat.add_comm, hxz] using r.equation
  have hac_lt : r.a < r.c :=
    core_right_same_exponent_gap r.b_pos heq'
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have hfac := core_diff_factorization hac r.x
  have hsum :
      r.a ^ r.x + r.b ^ r.y =
        r.a ^ r.x + (r.c - r.a) * CoreDiffQuot r.c r.a r.x :=
    r.equation.trans (by simpa [hxz] using hfac.symm)
  exact Nat.add_left_cancel hsum

/-- Closed form of the recursive quotient at exponent four. -/
theorem coreDiffQuot_four
    (c a : Nat) :
    CoreDiffQuot c a 4 =
      (c + a) * (c ^ 2 + a ^ 2) := by
  simp [CoreDiffQuot, Nat.pow_succ, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/--
Exact quartic factorization in the x=z=4 orientation:
  b^y = (c-a)(c+a)(c^2+a^2).
-/
theorem reduced_xz_four_exact_factorization
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4) :
    r.b ^ r.y =
      (r.c - r.a) * ((r.c + r.a) * (r.c ^ 2 + r.a ^ 2)) := by
  have hEq := reduced_x_eq_z_exact_factor r (hx.trans hz.symm)
  rw [hx, coreDiffQuot_four] at hEq
  exact hEq

/--
Symmetric exact quartic factorization in the y=z=4 orientation.
-/
theorem reduced_yz_four_exact_factorization
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4) :
    r.a ^ r.x =
      (r.c - r.b) * ((r.c + r.b) * (r.c ^ 2 + r.b ^ 2)) := by
  have hEq := reduced_y_eq_z_exact_factor r (hy.trans hz.symm)
  rw [hy, coreDiffQuot_four] at hEq
  exact hEq

private theorem dvd_mul_right_local
    {p a b : Nat}
    (h : p ∣ a) :
    p ∣ a * b := by
  rcases h with ⟨k, hk⟩
  refine ⟨k * b, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc]

private theorem dvd_mul_left_local
    {p a b : Nat}
    (h : p ∣ b) :
    p ∣ a * b := by
  rcases h with ⟨k, hk⟩
  refine ⟨a * k, ?_⟩
  rw [hk]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private def quarticData (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

private theorem quarticPairwise
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro h
    exact r.no_common (ab_pair_forces_common (quarticData r) h)
  · constructor
    · intro h
      exact r.no_common (ac_pair_forces_common (quarticData r) h)
    · intro h
      exact r.no_common (bc_pair_forces_common (quarticData r) h)

/-- Every prime dividing c-a on x=z=4 divides b. -/
theorem reduced_xz_four_sub_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c - r.a) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_right_local hdiv
  exact prime_dvd_pow_reflect hp hpow

/-- Every prime dividing c+a on x=z=4 divides b. -/
theorem reduced_xz_four_add_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c + r.a) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hinner : p ∣ (r.c + r.a) * (r.c ^ 2 + r.a ^ 2) :=
    dvd_mul_right_local hdiv
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

/-- Every prime dividing c^2+a^2 on x=z=4 divides b. -/
theorem reduced_xz_four_quad_prime_supports_b
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c ^ 2 + r.a ^ 2) :
    p ∣ r.b := by
  have hfac := reduced_xz_four_exact_factorization r hx hz
  have hinner : p ∣ (r.c + r.a) * (r.c ^ 2 + r.a ^ 2) :=
    dvd_mul_left_local hdiv
  have hpow : p ∣ r.b ^ r.y := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

/--
No odd prime divides both c-a and c+a on x=z=4.
-/ 
theorem reduced_xz_four_linear_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c + r.a) := by
  intro h
  rcases h with ⟨hminus, hplus⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have h2a : p ∣ 2 * r.a := by
    have hsub : p ∣ (r.c + r.a) - (r.c - r.a) :=
      Nat.dvd_sub hplus hminus
    have hid : (r.c + r.a) - (r.c - r.a) = 2 * r.a := by
      omega
    simpa [hid] using hsub
  have hpa : p ∣ r.a := by
    rcases prime_dvd_mul_local hp h2a with htwo | ha
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have hge : 2 ≤ p := Nat.succ_le_of_lt hp.1
      have heq : p = 2 := Nat.le_antisymm hle hge
      exact False.elim (hp2 heq)
    · exact ha
  have hpc : p ∣ r.c := by
    have hsub : p ∣ (r.c + r.a) - r.a :=
      Nat.dvd_sub hplus hpa
    simpa using hsub
  exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/-- Symmetric prime-support statements on y=z=4. -/
theorem reduced_yz_four_sub_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c - r.b) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_right_local hdiv
  exact prime_dvd_pow_reflect hp hpow

theorem reduced_yz_four_add_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c + r.b) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hinner : p ∣ (r.c + r.b) * (r.c ^ 2 + r.b ^ 2) :=
    dvd_mul_right_local hdiv
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

theorem reduced_yz_four_quad_prime_supports_a
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hdiv : p ∣ r.c ^ 2 + r.b ^ 2) :
    p ∣ r.a := by
  have hfac := reduced_yz_four_exact_factorization r hy hz
  have hinner : p ∣ (r.c + r.b) * (r.c ^ 2 + r.b ^ 2) :=
    dvd_mul_left_local hdiv
  have hpow : p ∣ r.a ^ r.x := by
    rw [hfac]
    exact dvd_mul_left_local hinner
  exact prime_dvd_pow_reflect hp hpow

/-- Closed form of the recursive quotient at exponent two. -/
private theorem coreDiffQuot_two
    (c a : Nat) :
    CoreDiffQuot c a 2 = c + a := by
  simp [CoreDiffQuot, Nat.pow_succ, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/--
No odd prime divides both c-a and c^2+a^2 on x=z=4.
-/
theorem reduced_xz_four_sub_quad_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  intro h
  rcases h with ⟨hsub, hquad⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have hfac2 := core_diff_factorization hac 2
  rw [coreDiffQuot_two] at hfac2
  have hprod : p ∣ (r.c - r.a) * (r.c + r.a) :=
    dvd_mul_right_local hsub
  have hdiffEq :
      r.c ^ 2 - r.a ^ 2 = (r.c - r.a) * (r.c + r.a) := by
    rw [← hfac2]
    exact Nat.add_sub_cancel_left _ _
  have hdiff : p ∣ r.c ^ 2 - r.a ^ 2 := by
    rw [hdiffEq]
    exact hprod
  have h2a2 : p ∣ 2 * (r.a ^ 2) := by
    have hs : p ∣ (r.c ^ 2 + r.a ^ 2) - (r.c ^ 2 - r.a ^ 2) :=
      Nat.dvd_sub hquad hdiff
    have hsqle : r.a ^ 2 ≤ r.c ^ 2 := by
      rw [← hfac2]
      exact Nat.le_add_right _ _
    have hcdecomp :
        r.c ^ 2 = (r.c ^ 2 - r.a ^ 2) + r.a ^ 2 :=
      (Nat.sub_add_cancel hsqle).symm
    have hid :
        (r.c ^ 2 + r.a ^ 2) - (r.c ^ 2 - r.a ^ 2) =
          2 * (r.a ^ 2) := by
      rw [hcdecomp]
      omega
    simpa [hid] using hs
  have hpa2 : p ∣ r.a ^ 2 := by
    rcases prime_dvd_mul_local hp h2a2 with htwo | ha2
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have hge : 2 ≤ p := Nat.succ_le_of_lt hp.1
      have heq : p = 2 := Nat.le_antisymm hle hge
      exact False.elim (hp2 heq)
    · exact ha2
  have hpa : p ∣ r.a := prime_dvd_pow_reflect hp hpa2
  have hpc : p ∣ r.c := by
    have hs : p ∣ (r.c - r.a) + r.a := Nat.dvd_add hsub hpa
    simpa [Nat.sub_add_cancel hac] using hs
  exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/--
No odd prime divides both c+a and c^2+a^2 on x=z=4.
-/
theorem reduced_xz_four_add_quad_odd_prime_disjoint
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c + r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  intro h
  rcases h with ⟨hadd, hquad⟩
  have hsq : p ∣ (r.c + r.a) * (r.c + r.a) :=
    dvd_mul_right_local hadd
  have hsumSq :
      (r.c + r.a) * (r.c + r.a) =
        r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2 := by
    simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.succ_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hfull : p ∣ r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2 := by
    rw [← hsumSq]
    exact hsq
  have h2ca : p ∣ 2 * r.c * r.a := by
    have hs :
        p ∣ (r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2) -
          (r.c ^ 2 + r.a ^ 2) :=
      Nat.dvd_sub hfull hquad
    have hid :
        (r.c ^ 2 + 2 * r.c * r.a + r.a ^ 2) -
          (r.c ^ 2 + r.a ^ 2) =
        2 * r.c * r.a := by
      omega
    simpa [hid] using hs
  rcases prime_dvd_mul_local hp h2ca with h2c | hpa
  · rcases prime_dvd_mul_local hp h2c with htwo | hpc
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have hge : 2 ≤ p := Nat.succ_le_of_lt hp.1
      have heq : p = 2 := Nat.le_antisymm hle hge
      exact hp2 heq
    ·
      have hpa' : p ∣ r.a := by
        have hs : p ∣ (r.c + r.a) - r.c := Nat.dvd_sub hadd hpc
        have hid : (r.c + r.a) - r.c = r.a :=
          Nat.add_sub_cancel_left r.c r.a
        simpa [hid] using hs
      exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa', hpc⟩
  ·
    have hpc : p ∣ r.c := by
      have hs : p ∣ (r.c + r.a) - r.a := Nat.dvd_sub hadd hpa
      have hid : (r.c + r.a) - r.a = r.c :=
        Nat.add_sub_cancel r.c r.a
      simpa [hid] using hs
    exact (quarticPairwise r).2.1 ⟨p, hp.1, hpa, hpc⟩

/--
The three quartic blocks on x=z=4 have pairwise disjoint odd-prime support.
-/
theorem reduced_xz_four_three_block_odd_prime_separation
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c + r.a) ∧
    ¬ (p ∣ r.c - r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) ∧
    ¬ (p ∣ r.c + r.a ∧ p ∣ r.c ^ 2 + r.a ^ 2) := by
  exact ⟨
    reduced_xz_four_linear_odd_prime_disjoint r hx hz hp hp2,
    reduced_xz_four_sub_quad_odd_prime_disjoint r hx hz hp hp2,
    reduced_xz_four_add_quad_odd_prime_disjoint r hx hz hp hp2
  ⟩

private theorem quartic_notEven_mod2_one
    (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hm hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem quarticExactlyOneEven
    (r : ReducedPrimitiveCandidate) :
    ExactlyOneEven r.a r.b r.c :=
  exactlyOneEven_of_pairwise (quarticData r) (quarticPairwise r)

/--
If a is the unique even base on x=z=4, all three quartic blocks are odd.
-/
theorem reduced_xz_four_a_even_blocks_odd
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    (r.c - r.a) % 2 = 1 ∧
    (r.c + r.a) % 2 = 1 ∧
    (r.c ^ 2 + r.a ^ 2) % 2 = 1 := by
  have hE := quarticExactlyOneEven r
  have hcOdd : r.c % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (quartic_notEven_mod2_one r.c).mp hA.2.2
    · exact False.elim (hB.1 ha)
    · exact False.elim (hC.1 ha)
  have ha0 : r.a % 2 = 0 := Nat.mod_eq_zero_of_dvd ha
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hac : r.a ≤ r.c := Nat.le_of_lt hac_lt
  have hsubOdd : (r.c - r.a) % 2 = 1 := by
    have hdecomp : (r.c - r.a) + r.a = r.c :=
      Nat.sub_add_cancel hac
    have hm := congrArg (fun n : Nat => n % 2) hdecomp
    change ((r.c - r.a) + r.a) % 2 = r.c % 2 at hm
    rw [Nat.add_mod, ha0, hcOdd] at hm
    omega
  have haddOdd : (r.c + r.a) % 2 = 1 := by
    rw [Nat.add_mod, hcOdd, ha0]
  have hc2 : r.c ^ 2 % 2 = 1 := by
    simp [Nat.pow_succ, Nat.mul_mod, hcOdd]
  have ha2 : r.a ^ 2 % 2 = 0 := by
    have hdiv : 2 ∣ r.a ^ 2 :=
      dvd_pow_of_dvd (by decide : 0 < (2 : Nat)) ha
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hquadOdd : (r.c ^ 2 + r.a ^ 2) % 2 = 1 := by
    rw [Nat.add_mod, hc2, ha2]
  exact ⟨hsubOdd, haddOdd, hquadOdd⟩

private theorem prime_ne_two_of_odd_divisor
    {p n : Nat}
    (hp : IsPrime p)
    (hnOdd : n % 2 = 1)
    (hpn : p ∣ n) :
    p ≠ 2 := by
  intro hp2
  subst p
  have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hpn
  omega

private theorem gcd_eq_one_of_no_common_prime
    {u v : Nat}
    (huPos : 0 < u)
    (hNo :
      ∀ p : Nat, IsPrime p → ¬ (p ∣ u ∧ p ∣ v)) :
    Nat.gcd u v = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdu hdv
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hdu with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt huPos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  rcases primeDivisorProperty_proved d hdgt with ⟨p, hp, hpd⟩
  have hpu : p ∣ u := nat_dvd_trans hpd hdu
  have hpv : p ∣ v := nat_dvd_trans hpd hdv
  exact False.elim (hNo p hp ⟨hpu, hpv⟩)

/--
On x=z=4 with a even, the three quartic blocks are pairwise coprime.
This is the exact UFD-ready packet needed before perfect-power splitting.
-/
theorem reduced_xz_four_a_even_block_gcd_packet
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    Nat.gcd (r.c - r.a) (r.c + r.a) = 1 ∧
    Nat.gcd (r.c - r.a) (r.c ^ 2 + r.a ^ 2) = 1 ∧
    Nat.gcd (r.c + r.a) (r.c ^ 2 + r.a ^ 2) = 1 := by
  have hOdd := reduced_xz_four_a_even_blocks_odd r hx hz ha
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hsubPos : 0 < r.c - r.a := Nat.zero_lt_sub_of_lt hac_lt
  have haddPos : 0 < r.c + r.a := by omega
  constructor
  · apply gcd_eq_one_of_no_common_prime hsubPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.1 hboth.1
    exact reduced_xz_four_linear_odd_prime_disjoint
      r hx hz hp hp2 hboth
  constructor
  · apply gcd_eq_one_of_no_common_prime hsubPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.1 hboth.1
    exact reduced_xz_four_sub_quad_odd_prime_disjoint
      r hx hz hp hp2 hboth
  · apply gcd_eq_one_of_no_common_prime haddPos
    intro p hp hboth
    have hp2 : p ≠ 2 :=
      prime_ne_two_of_odd_divisor hp hOdd.2.1 hboth.1
    exact reduced_xz_four_add_quad_odd_prime_disjoint
      r hx hz hp hp2 hboth

/--
Complete core-only quartic packet for the a-even x=z=4 orientation.
-/
structure XZFourAEvenCorePacket
    (r : ReducedPrimitiveCandidate) : Prop where
  hx : r.x = 4
  hz : r.z = 4
  ha : Even r.a
  factorization :
    r.b ^ r.y =
      (r.c - r.a) * ((r.c + r.a) * (r.c ^ 2 + r.a ^ 2))
  blocksOdd :
    (r.c - r.a) % 2 = 1 ∧
    (r.c + r.a) % 2 = 1 ∧
    (r.c ^ 2 + r.a ^ 2) % 2 = 1
  blocksCoprime :
    Nat.gcd (r.c - r.a) (r.c + r.a) = 1 ∧
    Nat.gcd (r.c - r.a) (r.c ^ 2 + r.a ^ 2) = 1 ∧
    Nat.gcd (r.c + r.a) (r.c ^ 2 + r.a ^ 2) = 1

def reduced_xz_four_a_even_core_packet
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (ha : Even r.a) :
    XZFourAEvenCorePacket r where
  hx := hx
  hz := hz
  ha := ha
  factorization := reduced_xz_four_exact_factorization r hx hz
  blocksOdd := reduced_xz_four_a_even_blocks_odd r hx hz ha
  blocksCoprime := reduced_xz_four_a_even_block_gcd_packet r hx hz ha

private theorem gcd_mul_eq_one_of_pairwise_gcd
    {A B C : Nat}
    (hAB : Nat.gcd A B = 1)
    (hAC : Nat.gcd A C = 1) :
    Nat.gcd A (B * C) = 1 := by
  by_cases hA0 : A = 0
  · subst A
    have hB1 : B = 1 := by simpa using hAB
    have hC1 : C = 1 := by simpa using hAC
    simp [hB1, hC1]
  apply (Nat.gcd_eq_one_iff).2
  intro d hdA hdBC
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hdA with ⟨k, hk⟩
    simp at hk
    exact hA0 hk
  have hdgt : 1 < d := by
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  rcases primeDivisorProperty_proved d hdgt with ⟨p, hp, hpd⟩
  have hpA : p ∣ A := nat_dvd_trans hpd hdA
  have hpBC : p ∣ B * C := nat_dvd_trans hpd hdBC
  rcases prime_dvd_mul_local hp hpBC with hpB | hpC
  · have hpG : p ∣ Nat.gcd A B := Nat.dvd_gcd hpA hpB
    rw [hAB] at hpG
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hpG
    exact False.elim ((Nat.not_le_of_gt hp.1) hle)
  · have hpG : p ∣ Nat.gcd A C := Nat.dvd_gcd hpA hpC
    rw [hAC] at hpG
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hpG
    exact False.elim ((Nat.not_le_of_gt hp.1) hle)

/--
Exact UFD producer actually needed by the (4,4,p) lane: the exponent is an
odd prime, not an arbitrary positive natural.
-/
def CoprimePairPrimePowerSplitting : Prop :=
  ∀ A B b p : Nat,
    OddPrimeExponent p →
    Nat.gcd A B = 1 →
    b ^ p = A * B →
    ∃ u v : Nat, A = u ^ p ∧ B = v ^ p

private theorem splitter_prime_pow_dvd_left
    {q A B k : Nat}
    (hq : IsPrime q)
    (hqB : ¬ q ∣ B)
    (h : q ^ k ∣ A * B) :
    q ^ k ∣ A := by
  induction k generalizing A with
  | zero =>
      simp
  | succ k ih =>
      have hqAB : q ∣ A * B := by
        rcases h with ⟨t, ht⟩
        refine ⟨q ^ k * t, ?_⟩
        rw [ht, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hqA : q ∣ A := by
        rcases prime_dvd_mul_local hq hqAB with hA | hB
        · exact hA
        · exact False.elim (hqB hB)
      rcases hqA with ⟨A1, hA⟩
      rcases h with ⟨t, ht⟩
      have hcancel : A1 * B = q ^ k * t := by
        have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq.1
        apply Nat.eq_of_mul_eq_mul_left hqpos
        calc
          q * (A1 * B) = (q * A1) * B := by simp [Nat.mul_assoc]
          _ = A * B := by rw [← hA]
          _ = q ^ (k + 1) * t := ht
          _ = q * (q ^ k * t) := by
                rw [Nat.pow_succ]
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hkA1 : q ^ k ∣ A1 :=
        ih (A := A1) ⟨t, hcancel⟩
      rcases hkA1 with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [hA, hs, Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem splitter_gcd_one_for_divisor_left
    {A A1 B : Nat}
    (hA1 : A1 ∣ A)
    (hAB : Nat.gcd A B = 1) :
    Nat.gcd A1 B = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdA1 hdB
  have hdA : d ∣ A := nat_dvd_trans hdA1 hA1
  have hdG : d ∣ Nat.gcd A B := Nat.dvd_gcd hdA hdB
  rw [hAB] at hdG
  exact Nat.dvd_one.mp hdG

private theorem splitter_pow_factor
    {q b b1 p : Nat}
    (hb : b = q * b1) :
    b ^ p = q ^ p * b1 ^ p := by
  rw [hb, Nat.mul_pow]

/--
Constructive core inhabitant of the prime-exponent coprime power splitter.
This avoids Nat.factorization and Mathlib.
-/
theorem coprimePairPrimePowerSplitting_resolved :
    CoprimePairPrimePowerSplitting := by
  intro A
  induction A using Nat.lt_wfRel.wf.induction with
  | h A ih =>
      intro B b p hp hAB hpow
      by_cases hA0 : A = 0
      · subst A
        have hB1 : B = 1 := by
          simpa using hAB
        have hb0 : b = 0 := by
          have hpow0 : b ^ p = 0 := by simpa using hpow
          cases b with
          | zero => rfl
          | succ n =>
              have hpos : 0 < (n + 1) ^ p :=
                Nat.pow_pos (Nat.succ_pos n)
              rw [hpow0] at hpos
              exact False.elim (Nat.lt_irrefl 0 hpos)
        refine ⟨0, 1, ?_, ?_⟩
        · subst b
          cases p with
          | zero =>
              have : ¬ 2 < 0 := Nat.not_lt_zero 2
              exact False.elim (this hp.2)
          | succ p =>
              simp
        · simpa [hB1]
      by_cases hA1 : A = 1
      · subst A
        have hBpow : B = b ^ p := by
          simpa using hpow.symm
        exact ⟨1, b, by simp, hBpow⟩
      have hAgt : 1 < A := by
        have hApos : 0 < A := Nat.pos_of_ne_zero hA0
        omega
      rcases primeDivisorProperty_proved A hAgt with ⟨q, hq, hqA⟩
      have hqB : ¬ q ∣ B := by
        intro hdivB
        have hdivG : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hdivB
        rw [hAB] at hdivG
        have hle : q ≤ 1 :=
          Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hdivG
        exact (Nat.not_le_of_gt hq.1) hle
      have hqBpow : q ∣ b ^ p := by
        rw [hpow]
        rcases hqA with ⟨k, hk⟩
        refine ⟨k * B, ?_⟩
        rw [hk]
        simp [Nat.mul_assoc]
      have hqb : q ∣ b := prime_dvd_pow_reflect hq hqBpow
      rcases hqb with ⟨b1, hb⟩
      have hqp_bpow : q ^ p ∣ b ^ p := by
        refine ⟨b1 ^ p, ?_⟩
        exact splitter_pow_factor hb
      have hqp_AB : q ^ p ∣ A * B := by
        rw [← hpow]
        exact hqp_bpow
      have hqp_A : q ^ p ∣ A :=
        splitter_prime_pow_dvd_left hq hqB hqp_AB
      rcases hqp_A with ⟨A1, hAeq⟩
      have hqppos : 0 < q ^ p :=
        Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one hq.1)
      have hA1lt : A1 < A := by
        have hqpgt : 1 < q ^ p := by
          have hpPos : 0 < p :=
            Nat.lt_trans (by decide : 0 < 2) hp.2
          have hqq : q ∣ q := ⟨1, (Nat.mul_one q).symm⟩
          have hqpow : q ∣ q ^ p := dvd_pow_of_dvd hpPos hqq
          have hqle : q ≤ q ^ p :=
            Nat.le_of_dvd hqppos hqpow
          exact Nat.lt_of_lt_of_le hq.1 hqle
        have hA1pos : 0 < A1 := by
          cases A1 with
          | zero =>
              simp at hAeq
              exact False.elim (hA0 hAeq)
          | succ n => exact Nat.succ_pos n
        rw [hAeq]
        have hlt :
            1 * A1 < (q ^ p) * A1 :=
          Nat.mul_lt_mul_of_pos_right hqpgt hA1pos
        simpa using hlt
      have hA1dvdA : A1 ∣ A := by
        refine ⟨q ^ p, ?_⟩
        rw [hAeq, Nat.mul_comm]
      have hA1B : Nat.gcd A1 B = 1 :=
        splitter_gcd_one_for_divisor_left hA1dvdA hAB
      have hbpow : b ^ p = q ^ p * b1 ^ p :=
        splitter_pow_factor hb
      have hcancel : b1 ^ p = A1 * B := by
        apply Nat.eq_of_mul_eq_mul_left hqppos
        calc
          q ^ p * b1 ^ p = b ^ p := hbpow.symm
          _ = A * B := hpow
          _ = (q ^ p * A1) * B := by rw [hAeq]
          _ = q ^ p * (A1 * B) := by rw [Nat.mul_assoc]
      rcases ih A1 hA1lt B b1 p hp hA1B hcancel with
        ⟨u, v, hA1pow, hBpow⟩
      refine ⟨q * u, v, ?_, hBpow⟩
      calc
        A = q ^ p * A1 := hAeq
        _ = q ^ p * u ^ p := by rw [hA1pow]
        _ = (q * u) ^ p := by rw [Nat.mul_pow]



/--
The prime-exponent pair splitter suffices for the quartic triple whenever the
common exponent is an odd prime.
-/
theorem primePairSplitter_quartic_triple
    (hPair : CoprimePairPrimePowerSplitting)
    (A B C b p : Nat)
    (hp : OddPrimeExponent p)
    (hAB : Nat.gcd A B = 1)
    (hAC : Nat.gcd A C = 1)
    (hBC : Nat.gcd B C = 1)
    (hpow : b ^ p = A * (B * C)) :
    ∃ u v w : Nat,
      A = u ^ p ∧
      B = v ^ p ∧
      C = w ^ p := by
  have hA_BC : Nat.gcd A (B * C) = 1 :=
    gcd_mul_eq_one_of_pairwise_gcd hAB hAC
  rcases hPair A (B * C) b p hp hA_BC hpow with
    ⟨u, t, hA, hBCpow⟩
  rcases hPair B C t p hp hBC hBCpow.symm with
    ⟨v, w, hB, hC⟩
  exact ⟨u, v, w, hA, hB, hC⟩

/--
The exact quartic identity used to reach the Dénes equation.
-/
theorem core_quartic_linear_square_sum
    {a c : Nat}
    (hac : a ≤ c) :
    (c - a) ^ 2 + (c + a) ^ 2 = 2 * (c ^ 2 + a ^ 2) := by
  let d := c - a
  have hc : c = d + a := by
    dsimp [d]
    exact (Nat.sub_add_cancel hac).symm
  rw [hc]
  dsimp [d]
  simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

private theorem pow_square_swap
    (u p : Nat) :
    (u ^ p) ^ 2 = (u ^ 2) ^ p := by
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  rw [Nat.mul_comm p 2]

/--
Prime-exponent UFD splitting turns the a-even x=z=4 branch into the concrete
Dénes equation (u^2)^p + (v^2)^p = 2*w^p.
-/
theorem reduced_xz_four_a_even_to_denes_equation
    (hPair : CoprimePairPrimePowerSplitting)
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hy : OddPrimeExponent r.y)
    (ha : Even r.a) :
    ∃ X Y Z : Nat,
      X ^ r.y + Y ^ r.y = 2 * Z ^ r.y := by
  have P := reduced_xz_four_a_even_core_packet r hx hz ha
  rcases primePairSplitter_quartic_triple
      hPair
      (r.c - r.a)
      (r.c + r.a)
      (r.c ^ 2 + r.a ^ 2)
      r.b
      r.y
      hy
      P.blocksCoprime.1
      P.blocksCoprime.2.1
      P.blocksCoprime.2.2
      P.factorization with
    ⟨u, v, w, hsub, hadd, hquad⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hid := core_quartic_linear_square_sum (Nat.le_of_lt hac_lt)
  rw [hsub, hadd, hquad] at hid
  refine ⟨u ^ 2, v ^ 2, w, ?_⟩
  rw [pow_square_swap u r.y, pow_square_swap v r.y] at hid
  simpa [Nat.mul_comm] using hid

private theorem splitter_pow_two_dvd_pow_prime
    {u p : Nat}
    (hp : 2 < p) :
    u ^ 2 ∣ u ^ p := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, p = 2 + k := by
    refine ⟨p - 2, ?_⟩
    omega
  refine ⟨u ^ k, ?_⟩
  rw [hk, Nat.pow_add]

private theorem splitter_gcd_one_of_two_divisors
    {A A' B B' : Nat}
    (hA : A' ∣ A)
    (hB : B' ∣ B)
    (hAB : Nat.gcd A B = 1) :
    Nat.gcd A' B' = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdA hdB
  have hdA0 : d ∣ A := nat_dvd_trans hdA hA
  have hdB0 : d ∣ B := nat_dvd_trans hdB hB
  have hdG : d ∣ Nat.gcd A B := Nat.dvd_gcd hdA0 hdB0
  rw [hAB] at hdG
  exact Nat.dvd_one.mp hdG

private theorem square_injective_pos
    {u v : Nat}
    (hu : 0 < u)
    (hv : 0 < v)
    (h : u ^ 2 = v ^ 2) :
    u = v := by
  rcases Nat.le_total u v with huv | hvu
  · rcases Nat.eq_or_lt_of_le huv with huvEq | huvLt
    · exact huvEq
    · have h1 : u * u < v * u :=
        Nat.mul_lt_mul_of_pos_right huvLt hu
      have h2 : v * u < v * v :=
        Nat.mul_lt_mul_of_pos_left huvLt hv
      have hlt : u ^ 2 < v ^ 2 := by
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using Nat.lt_trans h1 h2
      rw [h] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)
  · rcases Nat.eq_or_lt_of_le hvu with hvuEq | hvuLt
    · exact hvuEq.symm
    · have h1 : v * v < u * v :=
        Nat.mul_lt_mul_of_pos_right hvuLt hv
      have h2 : u * v < u * u :=
        Nat.mul_lt_mul_of_pos_left hvuLt hu
      have hlt : v ^ 2 < u ^ 2 := by
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using Nat.lt_trans h1 h2
      rw [← h] at hlt
      exact False.elim (Nat.lt_irrefl _ hlt)

private theorem pos_of_pow_pos_local
    {u p : Nat}
    (hp : 0 < p)
    (h : 0 < u ^ p) :
    0 < u := by
  cases u with
  | zero =>
      cases p with
      | zero =>
          exact False.elim ((Nat.not_lt_zero 0) hp)
      | succ p =>
          have h00 : 0 < 0 := by
            simpa using h
          exact False.elim (Nat.lt_irrefl 0 h00)
  | succ n =>
      exact Nat.succ_pos n

/-- Positive primitive nontrivial Dénes datum. -/
structure PrimitiveDenesSolutionCore (n : Nat) where
  X : Nat
  Y : Nat
  Z : Nat
  X_pos : 0 < X
  Y_pos : 0 < Y
  Z_pos : 0 < Z
  equation : X ^ n + Y ^ n = 2 * Z ^ n
  primitive : Nat.gcd X (Nat.gcd Y Z) = 1
  nontrivial : ¬ (X = Y ∧ Y = Z)

/--
The resolved core UFD splitter produces a genuine primitive nontrivial Dénes
solution from the a-even x=z=4 branch.
-/
theorem reduced_xz_four_a_even_to_primitive_denes_resolved
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hy : OddPrimeExponent r.y)
    (ha : Even r.a) :
    Nonempty (PrimitiveDenesSolutionCore r.y) := by
  have P := reduced_xz_four_a_even_core_packet r hx hz ha
  rcases primePairSplitter_quartic_triple
      coprimePairPrimePowerSplitting_resolved
      (r.c - r.a)
      (r.c + r.a)
      (r.c ^ 2 + r.a ^ 2)
      r.b
      r.y
      hy
      P.blocksCoprime.1
      P.blocksCoprime.2.1
      P.blocksCoprime.2.2
      P.factorization with
    ⟨u, v, w, hsub, hadd, hquad⟩
  have hac_lt : r.a < r.c := by
    have heq' : r.b ^ r.y + r.a ^ r.x = r.c ^ r.z := by
      simpa [Nat.add_comm] using r.equation
    exact core_right_same_exponent_gap r.b_pos (by simpa [hx, hz] using heq')
  have hsubPos : 0 < r.c - r.a := Nat.zero_lt_sub_of_lt hac_lt
  have haddPos : 0 < r.c + r.a := by omega
  have hquadPos : 0 < r.c ^ 2 + r.a ^ 2 := by
    have hc2 : 0 < r.c ^ 2 := Nat.pow_pos r.c_pos
    omega
  have huPos : 0 < u := by
    have hup : 0 < u ^ r.y := by simpa [hsub] using hsubPos
    exact pos_of_pow_pos_local (Nat.lt_trans (by decide : 0 < 2) hy.2) hup
  have hvPos : 0 < v := by
    have hvp : 0 < v ^ r.y := by simpa [hadd] using haddPos
    exact pos_of_pow_pos_local (Nat.lt_trans (by decide : 0 < 2) hy.2) hvp
  have hwPos : 0 < w := by
    have hwp : 0 < w ^ r.y := by simpa [hquad] using hquadPos
    exact pos_of_pow_pos_local (Nat.lt_trans (by decide : 0 < 2) hy.2) hwp
  let X := u ^ 2
  let Y := v ^ 2
  let Z := w
  have hEq : X ^ r.y + Y ^ r.y = 2 * Z ^ r.y := by
    have hid := core_quartic_linear_square_sum (Nat.le_of_lt hac_lt)
    rw [hsub, hadd, hquad] at hid
    rw [pow_square_swap u r.y, pow_square_swap v r.y] at hid
    simpa [X, Y, Z, Nat.mul_comm] using hid
  have hXYg : Nat.gcd X Y = 1 := by
    have hu2 : u ^ 2 ∣ u ^ r.y :=
      splitter_pow_two_dvd_pow_prime hy.2
    have hv2 : v ^ 2 ∣ v ^ r.y :=
      splitter_pow_two_dvd_pow_prime hy.2
    have huvPow : Nat.gcd (u ^ r.y) (v ^ r.y) = 1 := by
      simpa [hsub, hadd] using P.blocksCoprime.1
    simpa [X, Y] using
      (splitter_gcd_one_of_two_divisors hu2 hv2 huvPow)
  have hprimitive : Nat.gcd X (Nat.gcd Y Z) = 1 := by
    have hdiv : Nat.gcd X (Nat.gcd Y Z) ∣ Nat.gcd X Y := by
      apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_left _ _
      · exact nat_dvd_trans
          (Nat.gcd_dvd_right X (Nat.gcd Y Z))
          (Nat.gcd_dvd_left Y Z)
    have hone : Nat.gcd X (Nat.gcd Y Z) ∣ 1 := by
      simpa [hXYg] using hdiv
    exact Nat.dvd_one.mp hone
  have hneqXY : X ≠ Y := by
    intro hXY
    have huv : u = v := by
      apply square_injective_pos huPos hvPos
      simpa [X, Y] using hXY
    have hsumeq : r.c - r.a = r.c + r.a := by
      rw [hsub, hadd, huv]
    have ha0 : r.a = 0 := by omega
    exact (Nat.ne_of_gt r.a_pos) ha0
  exact ⟨{
    X := X
    Y := Y
    Z := Z
    X_pos := Nat.pow_pos huPos
    Y_pos := Nat.pow_pos hvPos
    Z_pos := hwPos
    equation := hEq
    primitive := hprimitive
    nontrivial := by
      intro h
      exact hneqXY h.1
  }⟩

/--
Deep terminal producer, stated in the exact Darmon–Merel shape needed here:
no primitive nontrivial solution of X^p + Y^p = 2 Z^p for odd prime p.
-/
def DenesOddPrimePrimitiveExclusion : Prop :=
  ∀ p : Nat, OddPrimeExponent p →
    ∀ S : PrimitiveDenesSolutionCore p, False

/--
Once the exact Darmon–Merel exclusion is supplied, the a-even x=z=4 branch is
impossible.  All preceding arithmetic is kernel-produced.
-/
theorem reduced_xz_four_a_even_eliminated_of_denes
    (hDenes : DenesOddPrimePrimitiveExclusion)
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hy : OddPrimeExponent r.y)
    (ha : Even r.a) :
    False := by
  rcases reduced_xz_four_a_even_to_primitive_denes_resolved
      r hx hz hy ha with ⟨S⟩
  exact hDenes r.y hy S

/--
Swap the two summands of a reduced primitive Beal candidate.  This is a genuine
symmetry of the equation and preserves every reduced-candidate field.
-/
def ReducedPrimitiveCandidate.swapAB
    (r : ReducedPrimitiveCandidate) : ReducedPrimitiveCandidate where
  a := r.b
  b := r.a
  c := r.c
  x := r.y
  y := r.x
  z := r.z
  a_pos := r.b_pos
  b_pos := r.a_pos
  c_pos := r.c_pos
  x_reduced := r.y_reduced
  y_reduced := r.x_reduced
  z_reduced := r.z_reduced
  equation := by simpa [Nat.add_comm] using r.equation
  no_common := by
    intro h
    rcases h with ⟨p, hp, hpb, hpa, hpc⟩
    exact r.no_common ⟨p, hp, hpa, hpb, hpc⟩

@[simp] theorem swapAB_a (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).a = r.b := rfl
@[simp] theorem swapAB_b (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).b = r.a := rfl
@[simp] theorem swapAB_c (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).c = r.c := rfl
@[simp] theorem swapAB_x (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).x = r.y := rfl
@[simp] theorem swapAB_y (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).y = r.x := rfl
@[simp] theorem swapAB_z (r : ReducedPrimitiveCandidate) :
    (ReducedPrimitiveCandidate.swapAB r).z = r.z := rfl

/--
Symmetric Dénes production: y=z=4 with b even reduces to the already-resolved
x=z=4/a-even branch after swapping the two summands.
-/
theorem reduced_yz_four_b_even_to_primitive_denes_resolved
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    (hxPrime : OddPrimeExponent r.x)
    (hb : Even r.b) :
    Nonempty (PrimitiveDenesSolutionCore r.x) := by
  have hs :
      Nonempty (PrimitiveDenesSolutionCore (ReducedPrimitiveCandidate.swapAB r).y) :=
    reduced_xz_four_a_even_to_primitive_denes_resolved
      (ReducedPrimitiveCandidate.swapAB r)
      (by simpa using hy)
      (by simpa using hz)
      (by simpa using hxPrime)
      (by simpa using hb)
  simpa using hs

/--
Darmon–Merel therefore also eliminates the symmetric y=z=4/b-even cell.
-/
theorem reduced_yz_four_b_even_eliminated_of_denes
    (hDenes : DenesOddPrimePrimitiveExclusion)
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    (hxPrime : OddPrimeExponent r.x)
    (hb : Even r.b) :
    False := by
  rcases reduced_yz_four_b_even_to_primitive_denes_resolved
      r hy hz hxPrime hb with ⟨S⟩
  exact hDenes r.x hxPrime S

/--
Elementary core-only impossibility: if x=y=4, c cannot be the unique even base.
-/
private theorem quartic_pow_mod_congr_local
    {a b m e : Nat}
    (h : a % m = b % m) :
    a ^ e % m = b ^ e % m := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod, ih, h]
      simp

private theorem quartic_odd_fourth_mod8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 4 % 8 = 1 := by
  have hres :
      n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hpar : (n % 8) % 2 = 1 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    omega
  rcases hres with h | h | h | h
  all_goals
    have hc : n ^ 4 % 8 = (n % 8) ^ 4 % 8 := by
      apply quartic_pow_mod_congr_local
      simp
    rw [hc, h]

private theorem quartic_even_pow_mod8
    {n e : Nat}
    (hn : Even n)
    (he : 2 < e) :
    n ^ e % 8 = 0 := by
  rcases hn with ⟨k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, e = m + 3 := by
    refine ⟨e - 3, ?_⟩
    omega
  rw [hk, hm]
  simp [Nat.pow_add, Nat.mul_pow, Nat.mul_mod,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem reduced_xy_four_c_even_impossible
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hc : Even r.c) :
    False := by
  have hE := quarticExactlyOneEven r
  have haOdd : r.a % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact False.elim (hA.2.2 hc)
    · exact (quartic_notEven_mod2_one r.a).mp hB.1
    · exact (quartic_notEven_mod2_one r.a).mp hC.1
  have hbOdd : r.b % 2 = 1 := by
    rcases hE with hA | hB | hC
    · exact (quartic_notEven_mod2_one r.b).mp hA.2.1
    · exact False.elim (hB.2.2 hc)
    · exact (quartic_notEven_mod2_one r.b).mp hC.2.1
  have hA8 : r.a ^ 4 % 8 = 1 := quartic_odd_fourth_mod8 haOdd
  have hB8 : r.b ^ 4 % 8 = 1 := quartic_odd_fourth_mod8 hbOdd
  have hC8 : r.c ^ r.z % 8 = 0 :=
    quartic_even_pow_mod8 hc r.z_reduced.1
  have hmod := congrArg (fun n : Nat => n % 8) r.equation
  have hbad : (1 + 1) % 8 = 0 := by
    simpa [hx, hy, Nat.add_mod, hA8, hB8, hC8] using hmod
  simp at hbad

/--
After the two Dénes cells and the elementary c-even x=y=4 cell are removed,
every remaining TwoFourPrime candidate lies in one of only three symmetry
orbits.
-/
def TwoFourResidualOrbit (r : ReducedPrimitiveCandidate) : Prop :=
  -- Orbit A: x=y=4 and the unique even base is on the left.
  (r.x = 4 ∧ r.y = 4 ∧ OddPrimeExponent r.z ∧
    (Even r.a ∨ Even r.b)) ∨
  -- Orbit B: the prime exponent is on the left summand; the other left base is even.
  ((r.x = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.y ∧ Even r.b) ∨
   (r.y = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.x ∧ Even r.a)) ∨
  -- Orbit C: z=4 and c is the unique even base.
  ((r.x = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.y ∧ Even r.c) ∨
   (r.y = 4 ∧ r.z = 4 ∧ OddPrimeExponent r.x ∧ Even r.c))

/--
Conditional exact compression of Q3: Darmon–Merel reduces all of
TwoFourPrime to the three residual symmetry orbits above.
-/
theorem twoFourPrime_reduces_to_three_orbits_of_denes
    (hDenes : DenesOddPrimePrimitiveExclusion)
    (r : ReducedPrimitiveCandidate)
    (h : TwoFourPrime r.x r.y r.z) :
    TwoFourResidualOrbit r := by
  have hE := quarticExactlyOneEven r
  rcases h with hxy | hxz | hyz
  · rcases hxy with ⟨hx, hy, hzPrime⟩
    rcases hE with hA | hB | hC
    · exact Or.inl ⟨hx, hy, hzPrime, Or.inl hA.1⟩
    · exact Or.inl ⟨hx, hy, hzPrime, Or.inr hB.2.1⟩
    · exact False.elim
        (reduced_xy_four_c_even_impossible r hx hy hC.2.2)
  · rcases hxz with ⟨hx, hz, hyPrime⟩
    rcases hE with hA | hB | hC
    · exact False.elim
        (reduced_xz_four_a_even_eliminated_of_denes
          hDenes r hx hz hyPrime hA.1)
    · exact Or.inr (Or.inl (Or.inl ⟨hx, hz, hyPrime, hB.2.1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hx, hz, hyPrime, hC.2.2⟩))
  · rcases hyz with ⟨hy, hz, hxPrime⟩
    rcases hE with hA | hB | hC
    · exact Or.inr (Or.inl (Or.inr ⟨hy, hz, hxPrime, hA.1⟩))
    · exact False.elim
        (reduced_yz_four_b_even_eliminated_of_denes
          hDenes r hy hz hxPrime hB.2.1)
    · exact Or.inr (Or.inr (Or.inr ⟨hy, hz, hxPrime, hC.2.2⟩))

private theorem quartic_oddPrime_mod2_one
    {p : Nat}
    (hp : OddPrimeExponent p) :
    p % 2 = 1 := by
  have hnot : ¬ 2 ∣ p := by
    intro h2
    rcases hp.1.2 2 h2 with h1 | hp2
    · cases h1
    · have hlt : 2 < 2 := by simpa [hp2] using hp.2
      exact Nat.lt_irrefl 2 hlt
  have hpos : 0 < p % 2 := Nat.emod_pos_of_not_dvd hnot
  have hlt : p % 2 < 2 := Nat.mod_lt p (by decide)
  omega

private theorem quartic_mod2_one_repr
    {e : Nat}
    (he : e % 2 = 1) :
    ∃ k : Nat, e = 2 * k + 1 := by
  refine ⟨e / 2, ?_⟩
  have h := Nat.mod_add_div e 2
  rw [he] at h
  omega

private theorem quartic_odd_square_mod8
    {n : Nat}
    (hn : n % 2 = 1) :
    n ^ 2 % 8 = 1 := by
  have hres :
      n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hpar : (n % 8) % 2 = 1 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans hn
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    omega
  rcases hres with h | h | h | h
  all_goals
    have hc : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := by
      apply quartic_pow_mod_congr_local
      simp
    rw [hc, h]

private theorem quartic_odd_pow_mod8_eq_base
    {n e : Nat}
    (hn : n % 2 = 1)
    (he : e % 2 = 1) :
    n ^ e % 8 = n % 8 := by
  rcases quartic_mod2_one_repr he with ⟨k, hk⟩
  rw [hk]
  have hs : n ^ 2 % 8 = 1 := quartic_odd_square_mod8 hn
  have hkpow : (n ^ 2) ^ k % 8 = 1 := by
    have hc := quartic_pow_mod_congr_local
      (a := n ^ 2) (b := 1) (m := 8) (e := k) hs
    simpa using hc
  calc
    n ^ (2 * k + 1) % 8
        = ((n ^ 2) ^ k * n) % 8 := by
            simp [Nat.pow_add, Nat.pow_mul]
    _ = (((n ^ 2) ^ k % 8) * (n % 8)) % 8 := by
            rw [Nat.mul_mod]
    _ = n % 8 := by
            rw [hkpow]
            simp

/--
Normalized arithmetic packet for the residual x=y=4, z=p orbit.
-/
structure XYFourPrimeOrbitPressure
    (r : ReducedPrimitiveCandidate) : Prop where
  hx : r.x = 4
  hy : r.y = 4
  hzPrime : OddPrimeExponent r.z
  leftEven : Even r.a ∨ Even r.b
  cOdd : r.c % 2 = 1
  cMod8 : r.c % 8 = 1
  pairwise : PairwisePrimitive r.a r.b r.c

/--
Every x=y=4 odd-prime candidate is forced into the normalized Orbit-A packet.
The c-even cell has already been eliminated.
-/
theorem reduced_xy_four_prime_orbit_pressure
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    XYFourPrimeOrbitPressure r := by
  have hE := quarticExactlyOneEven r
  have hcNot : ¬ Even r.c := by
    intro hc
    exact reduced_xy_four_c_even_impossible r hx hy hc
  have hcOdd : r.c % 2 = 1 :=
    (quartic_notEven_mod2_one r.c).mp hcNot
  have hleft : Even r.a ∨ Even r.b := by
    rcases hE with hA | hB | hC
    · exact Or.inl hA.1
    · exact Or.inr hB.2.1
    · exact False.elim (hcNot hC.2.2)
  have hRhs8 : r.c ^ r.z % 8 = 1 := by
    rcases hleft with ha | hb
    ·
      have hbOdd : r.b % 2 = 1 := by
        rcases hE with hA | hB | hC
        · exact (quartic_notEven_mod2_one r.b).mp hA.2.1
        · exact False.elim (hB.1 ha)
        · exact False.elim (hcNot hC.2.2)
      have hA8 : r.a ^ 4 % 8 = 0 :=
        quartic_even_pow_mod8 ha (by decide)
      have hB8 : r.b ^ 4 % 8 = 1 :=
        quartic_odd_fourth_mod8 hbOdd
      have hmod := congrArg (fun n : Nat => n % 8) r.equation
      simpa [hx, hy, Nat.add_mod, hA8, hB8] using hmod.symm
    ·
      have haOdd : r.a % 2 = 1 := by
        rcases hE with hA | hB | hC
        · exact False.elim (hA.2.1 hb)
        · exact (quartic_notEven_mod2_one r.a).mp hB.1
        · exact False.elim (hcNot hC.2.2)
      have hA8 : r.a ^ 4 % 8 = 1 :=
        quartic_odd_fourth_mod8 haOdd
      have hB8 : r.b ^ 4 % 8 = 0 :=
        quartic_even_pow_mod8 hb (by decide)
      have hmod := congrArg (fun n : Nat => n % 8) r.equation
      simpa [hx, hy, Nat.add_mod, hA8, hB8] using hmod.symm
  have hzOdd : r.z % 2 = 1 :=
    quartic_oddPrime_mod2_one hzPrime
  have hcPowBase :
      r.c ^ r.z % 8 = r.c % 8 :=
    quartic_odd_pow_mod8_eq_base hcOdd hzOdd
  have hc8 : r.c % 8 = 1 := by
    rw [← hcPowBase]
    exact hRhs8
  exact {
    hx := hx
    hy := hy
    hzPrime := hzPrime
    leftEven := hleft
    cOdd := hcOdd
    cMod8 := hc8
    pairwise := quarticPairwise r
  }

private theorem quartic_gcd3_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a (Nat.gcd r.b r.c) = 1 := by
  have hnot :
      ¬ 1 < Nat.gcd r.a (Nat.gcd r.b r.c) := by
    intro hgt
    have hex :
        ∃ q : Nat, CommonDivisor q r.a r.b r.c :=
      (commonDivisor_iff_one_lt_nestedGCD (quarticData r)).2 hgt
    exact r.no_common hex
  have hpos : 0 < Nat.gcd r.a (Nat.gcd r.b r.c) :=
    Nat.gcd_pos_of_pos_left (Nat.gcd r.b r.c) r.a_pos
  omega

/-- Concrete primitive solution of the generalized Fermat signature (4,4,p). -/
structure PrimitiveQuarticSumPrimeSolution (p : Nat) where
  A : Nat
  B : Nat
  C : Nat
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  primitive : Nat.gcd A (Nat.gcd B C) = 1
  equation : A ^ 4 + B ^ 4 = C ^ p

/-- Orbit A produces a genuine primitive (4,4,p) solution object. -/
theorem reduced_xy_four_prime_to_primitive_quartic_sum
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hy : r.y = 4)
    (hzPrime : OddPrimeExponent r.z) :
    Nonempty (PrimitiveQuarticSumPrimeSolution r.z) := by
  exact ⟨{
    A := r.a
    B := r.b
    C := r.c
    A_pos := r.a_pos
    B_pos := r.b_pos
    C_pos := r.c_pos
    primitive := quartic_gcd3_eq_one r
    equation := by simpa [hx, hy] using r.equation
  }⟩

/-- Concrete primitive solution of x^4 - y^4 = z^p, written subtraction-free. -/
structure PrimitiveQuarticDifferencePrimeSolution (p : Nat) where
  X : Nat
  Y : Nat
  Z : Nat
  X_pos : 0 < X
  Y_pos : 0 < Y
  Z_pos : 0 < Z
  primitiveXY : Nat.gcd X Y = 1
  equation : Y ^ 4 + Z ^ p = X ^ 4

private theorem quartic_gcd_ac_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.c r.a = 1 := by
  have hpw := quarticPairwise r
  apply gcd_eq_one_of_no_common_prime r.c_pos
  intro p hp hboth
  exact hpw.2.1 ⟨p, hp.1, hboth.2, hboth.1⟩

private theorem quartic_gcd_bc_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.c r.b = 1 := by
  have hpw := quarticPairwise r
  apply gcd_eq_one_of_no_common_prime r.c_pos
  intro p hp hboth
  exact hpw.2.2 ⟨p, hp.1, hboth.2, hboth.1⟩

/-- Every x=z=4 branch produces a primitive quartic-difference solution. -/
theorem reduced_xz_four_to_primitive_quartic_difference
    (r : ReducedPrimitiveCandidate)
    (hx : r.x = 4)
    (hz : r.z = 4)
    (hyPrime : OddPrimeExponent r.y) :
    Nonempty (PrimitiveQuarticDifferencePrimeSolution r.y) := by
  exact ⟨{
    X := r.c
    Y := r.a
    Z := r.b
    X_pos := r.c_pos
    Y_pos := r.a_pos
    Z_pos := r.b_pos
    primitiveXY := quartic_gcd_ac_eq_one r
    equation := by
      have h := r.equation
      simpa [hx, hz, Nat.add_comm] using h
  }⟩

/-- Every y=z=4 branch produces the symmetric quartic-difference solution. -/
theorem reduced_yz_four_to_primitive_quartic_difference
    (r : ReducedPrimitiveCandidate)
    (hy : r.y = 4)
    (hz : r.z = 4)
    (hxPrime : OddPrimeExponent r.x) :
    Nonempty (PrimitiveQuarticDifferencePrimeSolution r.x) := by
  exact ⟨{
    X := r.c
    Y := r.b
    Z := r.a
    X_pos := r.c_pos
    Y_pos := r.b_pos
    Z_pos := r.a_pos
    primitiveXY := quartic_gcd_bc_eq_one r
    equation := by
      simpa [hy, hz, Nat.add_comm] using r.equation
  }⟩

/--
Exact external formalization frontier for the known primitive (4,4,p)
generalized-Fermat exclusion.
-/
def PrimitiveQuarticSumPrimeExclusion : Prop :=
  ∀ p : Nat, OddPrimeExponent p →
    ∀ S : PrimitiveQuarticSumPrimeSolution p, False

/--
Exact external formalization frontier for the primitive quartic-difference
signature x^4-y^4=z^p.
-/
def PrimitiveQuarticDifferencePrimeExclusion : Prop :=
  ∀ p : Nat, OddPrimeExponent p →
    ∀ S : PrimitiveQuarticDifferencePrimeSolution p, False

/--
Q3 is now reduced exactly to the two classical generalized-Fermat
formalization frontiers above.
-/
theorem twoFourPrime_eliminated_of_quartic_exclusions
    (hSum : PrimitiveQuarticSumPrimeExclusion)
    (hDiff : PrimitiveQuarticDifferencePrimeExclusion) :
    ∀ r : ReducedPrimitiveCandidate,
      TwoFourPrime r.x r.y r.z → False := by
  intro r h
  rcases h with hxy | hxz | hyz
  · rcases hxy with ⟨hx, hy, hp⟩
    rcases reduced_xy_four_prime_to_primitive_quartic_sum
        r hx hy hp with ⟨S⟩
    exact hSum r.z hp S
  · rcases hxz with ⟨hx, hz, hp⟩
    rcases reduced_xz_four_to_primitive_quartic_difference
        r hx hz hp with ⟨S⟩
    exact hDiff r.y hp S
  · rcases hyz with ⟨hy, hz, hp⟩
    rcases reduced_yz_four_to_primitive_quartic_difference
        r hy hz hp with ⟨S⟩
    exact hDiff r.x hp S

#print axioms MCore.BealEffective.OpenMath.core_diff_factorization
#print axioms MCore.BealEffective.OpenMath.core_right_same_exponent_gap
#print axioms MCore.BealEffective.OpenMath.reduced_x_eq_z_exact_factor
#print axioms MCore.BealEffective.OpenMath.reduced_y_eq_z_exact_factor
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_exact_factorization
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_exact_factorization
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_sub_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_add_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_quad_prime_supports_b
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_linear_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_sub_prime_supports_a
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_add_prime_supports_a
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_quad_prime_supports_a
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_sub_quad_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_add_quad_odd_prime_disjoint
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_three_block_odd_prime_separation
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_blocks_odd
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_block_gcd_packet
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_core_packet
#print axioms MCore.BealEffective.OpenMath.coprimePairPrimePowerSplitting_resolved
#print axioms MCore.BealEffective.OpenMath.primePairSplitter_quartic_triple
#print axioms MCore.BealEffective.OpenMath.core_quartic_linear_square_sum
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_to_denes_equation
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_to_primitive_denes_resolved
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_a_even_eliminated_of_denes
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_b_even_to_primitive_denes_resolved
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_b_even_eliminated_of_denes
#print axioms MCore.BealEffective.OpenMath.reduced_xy_four_c_even_impossible
#print axioms MCore.BealEffective.OpenMath.twoFourPrime_reduces_to_three_orbits_of_denes
#print axioms MCore.BealEffective.OpenMath.reduced_xy_four_prime_orbit_pressure
#print axioms MCore.BealEffective.OpenMath.reduced_xy_four_prime_to_primitive_quartic_sum
#print axioms MCore.BealEffective.OpenMath.reduced_xz_four_to_primitive_quartic_difference
#print axioms MCore.BealEffective.OpenMath.reduced_yz_four_to_primitive_quartic_difference
#print axioms MCore.BealEffective.OpenMath.twoFourPrime_eliminated_of_quartic_exclusions

end OpenMath
end BealEffective
end MCore
