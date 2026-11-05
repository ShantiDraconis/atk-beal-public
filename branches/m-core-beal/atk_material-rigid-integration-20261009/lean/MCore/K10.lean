import MCore.K9

namespace MCore

/-- K10: every natural greater than one has a divisor satisfying the local
    `IsPrime` predicate. Constructive strong induction with bounded search. -/
theorem primeDivisorProperty_core : PrimeDivisorProperty := by
  intro n
  induction n using Nat.lt_wfRel.wf.induction with
  | h n ih =>
      intro hn
      let P : Nat → Prop := fun d => 1 < d ∧ d < n ∧ d ∣ n
      have instP (d : Nat) : Decidable (P d) := inferInstance
      let hex : Decidable (∃ d, d < n ∧ P d) := inferInstance
      match hex with
      | isTrue hproper =>
          obtain ⟨d, hdlt, hdgt1, _, hdn⟩ := hproper
          obtain ⟨p, hp, hpd⟩ := ih d hdlt hdgt1
          exact ⟨p, hp, nat_dvd_trans hpd hdn⟩
      | isFalse hproper =>
          have hprime : IsPrime n := by
            refine ⟨hn, ?_⟩
            intro d hdn
            by_cases hd1 : d = 1
            · exact Or.inl hd1
            · right
              have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
              have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
              have hdpos : 0 < d := by
                apply Nat.pos_of_ne_zero
                intro hd0
                rcases hdn with ⟨k, hk⟩
                subst d
                have hz : 0 * k = 0 := Nat.zero_mul k
                exact hn0 (hk.trans hz)
              have hdgt1 : 1 < d := by
                have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
                exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
              rcases hdn with ⟨k, hk⟩
              have hkpos : 0 < k := by
                apply Nat.pos_of_ne_zero
                intro hk0
                subst k
                exact hn0 hk
              have hdle : d ≤ n := by
                rw [hk]
                exact Nat.le_mul_of_pos_right d hkpos
              cases Nat.lt_or_eq_of_le hdle with
              | inl hdlt =>
                  have hbad : ∃ q, q < n ∧ P q := ⟨d, hdlt, hdgt1, hdlt, ⟨k, hk⟩⟩
                  exact False.elim (hproper hbad)
              | inr hdeq => exact hdeq
          have hdivself : n ∣ n := ⟨1, (Nat.mul_one n).symm⟩
          exact ⟨n, hprime, hdivself⟩

theorem primeDivisorProperty_proved : PrimeDivisorProperty :=
  primeDivisorProperty_core

theorem commonPrime_iff_commonDivisor {a b c : Nat} :
    CommonPrime a b c ↔ ∃ d : Nat, CommonDivisor d a b c :=
  commonPrime_iff_commonDivisor_of_primeDivisor primeDivisorProperty_proved

end MCore
