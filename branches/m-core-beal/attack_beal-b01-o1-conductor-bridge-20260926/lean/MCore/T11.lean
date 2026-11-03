import MCore.T10

namespace MCore

/-- A nontrivial divisor shared by two bases. -/
def T11PairCommonDivisor (q a b : Nat) : Prop :=
  1 < q ∧ q ∣ a ∧ q ∣ b

/-- Forward divisibility through a positive power, kept local and constructive. -/
theorem T11_dvd_pow_of_dvd
    {p a n : Nat} (hn : 0 < n) (hpa : p ∣ a) : p ∣ a ^ n := by
  cases n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n =>
      rcases hpa with ⟨k, hak⟩
      refine ⟨a ^ n * k, ?_⟩
      simp [Nat.pow_succ, hak, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Divisibility is closed under addition, with an explicit witness. -/
theorem T11_dvd_add
    {p u v : Nat} (hpu : p ∣ u) (hpv : p ∣ v) : p ∣ u + v := by
  rcases hpu with ⟨ku, hku⟩
  rcases hpv with ⟨kv, hkv⟩
  refine ⟨ku + kv, ?_⟩
  rw [hku, hkv, Nat.mul_add]

/-- If the first two bases share a nontrivial divisor, the equation forces a
    common prime divisor of all three bases. -/
theorem T11_ab_pair_forces_common
    {a b c x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpair : ∃ q : Nat, T11PairCommonDivisor q a b) :
    ∃ p : Nat, CommonDivisor p a b c := by
  rcases hpair with ⟨q, hqgt, hqa, hqb⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpa : p ∣ a := nat_dvd_trans hpq hqa
  have hpb : p ∣ b := nat_dvd_trans hpq hqb
  have hpax : p ∣ a ^ x := T11_dvd_pow_of_dvd hx hpa
  have hpby : p ∣ b ^ y := T11_dvd_pow_of_dvd hy hpb
  have hpcz : p ∣ c ^ z := by
    rw [← heq]
    exact T11_dvd_add hpax hpby
  have hpc : p ∣ c :=
    T9_primePowerReflection_proved p c z hp hpcz
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- If the first and third bases share a nontrivial divisor, subtraction from
    the exact equation forces the same prime into the second base. -/
theorem T11_ac_pair_forces_common
    {a b c x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpair : ∃ q : Nat, T11PairCommonDivisor q a c) :
    ∃ p : Nat, CommonDivisor p a b c := by
  rcases hpair with ⟨q, hqgt, hqa, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpa : p ∣ a := nat_dvd_trans hpq hqa
  have hpc : p ∣ c := nat_dvd_trans hpq hqc
  have hpax : p ∣ a ^ x := T11_dvd_pow_of_dvd hx hpa
  have hpcz : p ∣ c ^ z := T11_dvd_pow_of_dvd hz hpc
  have hpby : p ∣ b ^ y := by
    have hsub : p ∣ c ^ z - a ^ x := Nat.dvd_sub hpcz hpax
    have hdiff : c ^ z - a ^ x = b ^ y := by
      calc
        c ^ z - a ^ x = (a ^ x + b ^ y) - a ^ x :=
          congrArg (fun t : Nat => t - a ^ x) heq.symm
        _ = b ^ y := Nat.add_sub_cancel_left (a ^ x) (b ^ y)
    rw [hdiff] at hsub
    exact hsub
  have hpb : p ∣ b :=
    T9_primePowerReflection_proved p b y hp hpby
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- The symmetric second/third-base version. -/
theorem T11_bc_pair_forces_common
    {a b c x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hpair : ∃ q : Nat, T11PairCommonDivisor q b c) :
    ∃ p : Nat, CommonDivisor p a b c := by
  rcases hpair with ⟨q, hqgt, hqb, hqc⟩
  rcases primeDivisorProperty_proved q hqgt with ⟨p, hp, hpq⟩
  have hpb : p ∣ b := nat_dvd_trans hpq hqb
  have hpc : p ∣ c := nat_dvd_trans hpq hqc
  have hpby : p ∣ b ^ y := T11_dvd_pow_of_dvd hy hpb
  have hpcz : p ∣ c ^ z := T11_dvd_pow_of_dvd hz hpc
  have hpax : p ∣ a ^ x := by
    have hsub : p ∣ c ^ z - b ^ y := Nat.dvd_sub hpcz hpby
    have hdiff : c ^ z - b ^ y = a ^ x := by
      calc
        c ^ z - b ^ y = (a ^ x + b ^ y) - b ^ y :=
          congrArg (fun t : Nat => t - b ^ y) heq.symm
        _ = a ^ x := Nat.add_sub_cancel (a ^ x) (b ^ y)
    rw [hdiff] at hsub
    exact hsub
  have hpa : p ∣ a :=
    T9_primePowerReflection_proved p a x hp hpax
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- Pairwise primitiveness of the three bases. -/
def T11PairwisePrimitive (a b c : Nat) : Prop :=
  (¬ ∃ q : Nat, T11PairCommonDivisor q a b) ∧
  (¬ ∃ q : Nat, T11PairCommonDivisor q a c) ∧
  (¬ ∃ q : Nat, T11PairCommonDivisor q b c)

theorem T11_pairwise_of_primitive_equation
    {a b c x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hprimitive : ¬ ∃ q : Nat, CommonDivisor q a b c) :
    T11PairwisePrimitive a b c := by
  constructor
  · intro hpair
    exact hprimitive (T11_ab_pair_forces_common hx hy hz heq hpair)
  constructor
  · intro hpair
    exact hprimitive (T11_ac_pair_forces_common hx hy hz heq hpair)
  · intro hpair
    exact hprimitive (T11_bc_pair_forces_common hx hy hz heq hpair)

/-- T11 strengthens T10 to an equivalent reduced candidate whose bases are
    pairwise primitive, not merely free of a common divisor shared by all three. -/
def T11PairwiseReducedCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    T11PairwisePrimitive a b c

theorem T11_T10_to_pairwise :
    T10ReducedCandidate → T11PairwiseReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hprimitive⟩
  have hx0 : 0 < x := Nat.lt_trans (by decide : 0 < 2) hx.1
  have hy0 : 0 < y := Nat.lt_trans (by decide : 0 < 2) hy.1
  have hz0 : 0 < z := Nat.lt_trans (by decide : 0 < 2) hz.1
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq,
    T11_pairwise_of_primitive_equation hx0 hy0 hz0 heq hprimitive⟩

theorem T11_pairwise_to_T10 :
    T11PairwiseReducedCandidate → T10ReducedCandidate := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hpw⟩
  have hprimitive : ¬ ∃ q : Nat, CommonDivisor q a b c := by
    intro h
    rcases h with ⟨q, hqgt, hqa, hqb, hqc⟩
    exact hpw.1 ⟨q, hqgt, hqa, hqb⟩
  exact ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hprimitive⟩

theorem T11_candidate_iff_pairwise :
    T10ReducedCandidate ↔ T11PairwiseReducedCandidate :=
  ⟨T11_T10_to_pairwise, T11_pairwise_to_T10⟩

def T11PairwiseScientificFrontier : Prop :=
  ¬ T11PairwiseReducedCandidate

theorem T11_beal_iff_pairwise_frontier :
    BealConjecture ↔ T11PairwiseScientificFrontier := by
  rw [T10_beal_iff_reduced_frontier]
  unfold T10ReducedScientificFrontier T11PairwiseScientificFrontier
  exact not_congr T11_candidate_iff_pairwise

#print axioms MCore.T11_dvd_pow_of_dvd
#print axioms MCore.T11_ab_pair_forces_common
#print axioms MCore.T11_ac_pair_forces_common
#print axioms MCore.T11_bc_pair_forces_common
#print axioms MCore.T11_pairwise_of_primitive_equation
#print axioms MCore.T11_candidate_iff_pairwise
#print axioms MCore.T11_beal_iff_pairwise_frontier

end MCore
