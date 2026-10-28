import MCore.V012

namespace MCore

/-- T7 normal form for an exponent: after factoring an exponent > 2,
    it is enough to expose a factor which is either 4 or a prime > 2. -/
def T7ReducedExponent (r : Nat) : Prop :=
  2 < r ∧ (r = 4 ∨ IsPrime r)

def T7ExponentReduces (n : Nat) : Prop :=
  ∃ r k : Nat, n = r * k ∧ T7ReducedExponent r

private theorem T7_two_factor_gt_one
    {n k : Nat} (hk : n = 2 * k) (hn : 2 < n) : 1 < k := by
  cases k with
  | zero =>
      have hn0 : n = 0 := by simpa using hk
      subst n
      exact False.elim (Nat.not_lt_zero 2 hn)
  | succ k =>
      cases k with
      | zero =>
          have hn2 : n = 2 := by simpa using hk
          subst n
          exact False.elim (Nat.lt_irrefl 2 hn)
      | succ k =>
          exact Nat.succ_lt_succ (Nat.zero_lt_succ k)

/-- Every natural exponent > 2 has a divisor exponent > 2 which is either
    4 or prime. This is constructive and uses the certified K10
    prime-divisor kernel. -/
theorem T7_exponent_reduction
    {n : Nat} (hn : 2 < n) : T7ExponentReduces n := by
  have hn1 : 1 < n := Nat.lt_trans (by decide : 1 < 2) hn
  rcases primeDivisorProperty_proved n hn1 with ⟨p, hp, hpn⟩
  by_cases hp2 : p = 2
  · subst p
    rcases hpn with ⟨k, hk⟩
    have hk1 : 1 < k := T7_two_factor_gt_one hk hn
    rcases primeDivisorProperty_proved k hk1 with ⟨q, hq, hqk⟩
    by_cases hq2 : q = 2
    · subst q
      rcases hqk with ⟨m, hkm⟩
      refine ⟨4, m, ?_, ?_⟩
      · calc
          n = 2 * k := hk
          _ = 2 * (2 * m) := congrArg (fun t : Nat => 2 * t) hkm
          _ = (2 * 2) * m := (K9.Core.mul_assoc_core 2 2 m).symm
          _ = 4 * m := rfl
      · exact ⟨by decide, Or.inl rfl⟩
    · have h2le : 2 ≤ q := Nat.succ_le_of_lt hq.1
      have h2lt : 2 < q := Nat.lt_of_le_of_ne h2le (Ne.symm hq2)
      have hkn : k ∣ n := by
        refine ⟨2, ?_⟩
        calc
          n = 2 * k := hk
          _ = k * 2 := Nat.mul_comm 2 k
      have hqn : q ∣ n := nat_dvd_trans hqk hkn
      rcases hqn with ⟨m, hnm⟩
      exact ⟨q, m, hnm, h2lt, Or.inr hq⟩
  · have h2le : 2 ≤ p := Nat.succ_le_of_lt hp.1
    have h2lt : 2 < p := Nat.lt_of_le_of_ne h2le (Ne.symm hp2)
    rcases hpn with ⟨k, hnk⟩
    exact ⟨p, k, hnk, h2lt, Or.inr hp⟩

#print axioms MCore.T7_exponent_reduction

end MCore
