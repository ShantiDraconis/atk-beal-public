import MCore.BealEffective.ExactRemainingObligation
import MCore.K10
import Init.Data.Nat.Gcd

namespace MCore
namespace BealEffective

/-- Local Euclid kernel for the project's elementary IsPrime predicate. -/
theorem prime_dvd_mul_local
    {p a b : Nat}
    (hp : IsPrime p)
    (hab : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases (Nat.dvd_mul.mp hab) with ⟨p₁, p₂, hp₁a, hp₂b, hprod⟩
  have hp₁p : p₁ ∣ p := ⟨p₂, hprod.symm⟩
  rcases hp.2 p₁ hp₁p with hp₁one | hp₁eq
  · subst p₁
    have hp₂eq : p₂ = p := by simpa using hprod
    subst p₂
    exact Or.inr hp₂b
  · subst p₁
    exact Or.inl hp₁a

private theorem prime_not_dvd_one
    {p : Nat}
    (hp : IsPrime p) :
    ¬ p ∣ 1 := by
  intro h
  have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) h
  exact (Nat.not_le_of_gt hp.1) hle

/-- Prime divisibility reflects through powers. -/
theorem prime_dvd_pow_reflect
    {p a n : Nat}
    (hp : IsPrime p)
    (hpow : p ∣ a ^ n) :
    p ∣ a := by
  induction n with
  | zero =>
      have : p ∣ 1 := by simpa using hpow
      exact False.elim (prime_not_dvd_one hp this)
  | succ n ih =>
      have hmul : p ∣ a ^ n * a := by
        simpa [Nat.pow_succ] using hpow
      rcases prime_dvd_mul_local hp hmul with hprev | ha
      · exact ih hprev
      · exact ha

/-- Divisibility propagates to positive powers. -/
theorem dvd_pow_of_dvd
    {p a n : Nat}
    (hn : 0 < n)
    (hpa : p ∣ a) :
    p ∣ a ^ n := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n =>
      rcases hpa with ⟨k, hk⟩
      refine ⟨a ^ n * k, ?_⟩
      simp [Nat.pow_succ, hk, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def PairCommonDivisor (q a b : Nat) : Prop :=
  1 < q ∧ q ∣ a ∧ q ∣ b

def PairwisePrimitive (a b c : Nat) : Prop :=
  (¬ ∃ q : Nat, PairCommonDivisor q a b) ∧
  (¬ ∃ q : Nat, PairCommonDivisor q a c) ∧
  (¬ ∃ q : Nat, PairCommonDivisor q b c)

theorem ab_pair_forces_common
    (d : BealData)
    (hpair : ∃ q : Nat, PairCommonDivisor q d.a d.b) :
    ∃ p : Nat, CommonDivisor p d.a d.b d.c := by
  rcases hpair with ⟨q, hqgt, hqa, hqb⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpa : p ∣ d.a := nat_dvd_trans hpq hqa
  have hpb : p ∣ d.b := nat_dvd_trans hpq hqb
  have hpax : p ∣ d.a ^ d.x := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.x_gt_two) hpa
  have hpby : p ∣ d.b ^ d.y := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.y_gt_two) hpb
  have hpsum : p ∣ d.a ^ d.x + d.b ^ d.y := Nat.dvd_add hpax hpby
  have hpcz : p ∣ d.c ^ d.z := by simpa [d.equation] using hpsum
  have hpc : p ∣ d.c := prime_dvd_pow_reflect hp hpcz
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

theorem ac_pair_forces_common
    (d : BealData)
    (hpair : ∃ q : Nat, PairCommonDivisor q d.a d.c) :
    ∃ p : Nat, CommonDivisor p d.a d.b d.c := by
  rcases hpair with ⟨q, hqgt, hqa, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpa : p ∣ d.a := nat_dvd_trans hpq hqa
  have hpc : p ∣ d.c := nat_dvd_trans hpq hqc
  have hpax : p ∣ d.a ^ d.x := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.x_gt_two) hpa
  have hpcz : p ∣ d.c ^ d.z := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.z_gt_two) hpc
  have hpby : p ∣ d.b ^ d.y := by
    have hsub : p ∣ d.c ^ d.z - d.a ^ d.x := Nat.dvd_sub hpcz hpax
    have hdiff : d.c ^ d.z - d.a ^ d.x = d.b ^ d.y := by
      calc
        d.c ^ d.z - d.a ^ d.x =
            (d.a ^ d.x + d.b ^ d.y) - d.a ^ d.x := by rw [d.equation]
        _ = d.b ^ d.y := Nat.add_sub_cancel_left _ _
    simpa [hdiff] using hsub
  have hpb : p ∣ d.b := prime_dvd_pow_reflect hp hpby
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

theorem bc_pair_forces_common
    (d : BealData)
    (hpair : ∃ q : Nat, PairCommonDivisor q d.b d.c) :
    ∃ p : Nat, CommonDivisor p d.a d.b d.c := by
  rcases hpair with ⟨q, hqgt, hqb, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpb : p ∣ d.b := nat_dvd_trans hpq hqb
  have hpc : p ∣ d.c := nat_dvd_trans hpq hqc
  have hpby : p ∣ d.b ^ d.y := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.y_gt_two) hpb
  have hpcz : p ∣ d.c ^ d.z := dvd_pow_of_dvd (Nat.lt_trans (by decide : 0 < 2) d.z_gt_two) hpc
  have hpax : p ∣ d.a ^ d.x := by
    have hsub : p ∣ d.c ^ d.z - d.b ^ d.y := Nat.dvd_sub hpcz hpby
    have hdiff : d.c ^ d.z - d.b ^ d.y = d.a ^ d.x := by
      calc
        d.c ^ d.z - d.b ^ d.y =
            (d.a ^ d.x + d.b ^ d.y) - d.b ^ d.y := by rw [d.equation]
        _ = d.a ^ d.x := Nat.add_sub_cancel _ _
    simpa [hdiff] using hsub
  have hpa : p ∣ d.a := prime_dvd_pow_reflect hp hpax
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- A primitive Beal datum is automatically pairwise primitive. -/
theorem pairwisePrimitive_of_gcd3_eq_one
    (d : BealData)
    (hg : gcd3 d = 1) :
    PairwisePrimitive d.a d.b d.c := by
  have hNoCommon : ¬ ∃ p : Nat, CommonDivisor p d.a d.b d.c := by
    intro h
    have hlt := (commonDivisor_iff_one_lt_nestedGCD d).mp h
    unfold gcd3 at hg
    rw [hg] at hlt
    exact Nat.lt_irrefl 1 hlt
  constructor
  · intro hpair
    exact hNoCommon (ab_pair_forces_common d hpair)
  constructor
  · intro hpair
    exact hNoCommon (ac_pair_forces_common d hpair)
  · intro hpair
    exact hNoCommon (bc_pair_forces_common d hpair)

def Even (n : Nat) : Prop := 2 ∣ n

def ExactlyOneEven (a b c : Nat) : Prop :=
  (Even a ∧ ¬ Even b ∧ ¬ Even c) ∨
  (¬ Even a ∧ Even b ∧ ¬ Even c) ∨
  (¬ Even a ∧ ¬ Even b ∧ Even c)

private theorem not_even_iff_mod_two_eq_one (n : Nat) :
    (¬ Even n) ↔ n % 2 = 1 := by
  unfold Even
  constructor
  · intro h
    have hpos : 0 < n % 2 := Nat.emod_pos_of_not_dvd h
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  · intro hmod hdvd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega

private theorem odd_pow_mod_two
    {a n : Nat}
    (ha : a % 2 = 1) :
    a ^ n % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, ha]

theorem some_base_even (d : BealData) :
    Even d.a ∨ Even d.b ∨ Even d.c := by
  match Nat.decidable_dvd 2 d.a with
  | isTrue ha =>
      exact Or.inl ha
  | isFalse ha =>
      match Nat.decidable_dvd 2 d.b with
      | isTrue hb =>
          exact Or.inr (Or.inl hb)
      | isFalse hb =>
          match Nat.decidable_dvd 2 d.c with
          | isTrue hc =>
              exact Or.inr (Or.inr hc)
          | isFalse hc =>
              have hoa := (not_even_iff_mod_two_eq_one d.a).mp ha
              have hob := (not_even_iff_mod_two_eq_one d.b).mp hb
              have hoc := (not_even_iff_mod_two_eq_one d.c).mp hc
              have hax := odd_pow_mod_two (n := d.x) hoa
              have hby := odd_pow_mod_two (n := d.y) hob
              have hcz := odd_pow_mod_two (n := d.z) hoc
              have heq := congrArg (fun n : Nat => n % 2) d.equation
              have hleft : (d.a ^ d.x + d.b ^ d.y) % 2 = 0 := by
                rw [Nat.add_mod, hax, hby]
              change (d.a ^ d.x + d.b ^ d.y) % 2 = d.c ^ d.z % 2 at heq
              rw [hleft, hcz] at heq
              exact False.elim (Nat.zero_ne_one heq)

theorem exactlyOneEven_of_pairwise
    (d : BealData)
    (hpw : PairwisePrimitive d.a d.b d.c) :
    ExactlyOneEven d.a d.b d.c := by
  have hab : ¬ (Even d.a ∧ Even d.b) := by
    rintro ⟨ha, hb⟩
    exact hpw.1 ⟨2, by decide, ha, hb⟩
  have hac : ¬ (Even d.a ∧ Even d.c) := by
    rintro ⟨ha, hc⟩
    exact hpw.2.1 ⟨2, by decide, ha, hc⟩
  have hbc : ¬ (Even d.b ∧ Even d.c) := by
    rintro ⟨hb, hc⟩
    exact hpw.2.2 ⟨2, by decide, hb, hc⟩
  rcases some_base_even d with ha | hb | hc
  · exact Or.inl ⟨ha, (fun hb => hab ⟨ha,hb⟩), (fun hc => hac ⟨ha,hc⟩)⟩
  · exact Or.inr (Or.inl ⟨(fun ha => hab ⟨ha,hb⟩), hb, (fun hc => hbc ⟨hb,hc⟩)⟩)
  · exact Or.inr (Or.inr ⟨(fun ha => hac ⟨ha,hc⟩), (fun hb => hbc ⟨hb,hc⟩), hc⟩)

/-- Every hypothetical failure of the terminal lower bound is constrained to
the pairwise-primitive, exactly-one-even subdomain. -/
structure PrimitiveCounterexampleProfile (d : BealData) : Prop where
  gcd_one : gcd3 d = 1
  pairwise : PairwisePrimitive d.a d.b d.c
  exactly_one_even : ExactlyOneEven d.a d.b d.c

theorem failed_lowerBound_profiles
    (d : BealData)
    (h : ¬ 1 < gcd3 d) :
    PrimitiveCounterexampleProfile d := by
  have hg := gcd3_eq_one_of_not_lowerBound d h
  exact ⟨hg, pairwisePrimitive_of_gcd3_eq_one d hg,
    exactlyOneEven_of_pairwise d (pairwisePrimitive_of_gcd3_eq_one d hg)⟩

#print axioms MCore.BealEffective.prime_dvd_mul_local
#print axioms MCore.BealEffective.prime_dvd_pow_reflect
#print axioms MCore.BealEffective.pairwisePrimitive_of_gcd3_eq_one
#print axioms MCore.BealEffective.some_base_even
#print axioms MCore.BealEffective.exactlyOneEven_of_pairwise
#print axioms MCore.BealEffective.failed_lowerBound_profiles

end BealEffective
end MCore
