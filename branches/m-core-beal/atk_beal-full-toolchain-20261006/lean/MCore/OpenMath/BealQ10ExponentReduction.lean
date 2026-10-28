import MCore.OpenMath.BealQ10Parity
import MCore.K10

namespace MCore.OpenMath.BealQ10

/-- Reduced exponent normal form: either 4 or an odd prime. -/
def ReducedExponent (r : Nat) : Prop :=
  2 < r ∧ (r = 4 ∨ MCore.IsPrime r)

def ExponentReduces (n : Nat) : Prop :=
  ∃ r k : Nat, n = r * k ∧ ReducedExponent r

private theorem two_factor_gt_one
    {n k : Nat}
    (hk : n = 2 * k)
    (hn : 2 < n) :
    1 < k := by
  omega

/-- Constructive exponent reduction from the kernelized prime-divisor producer. -/
theorem exponent_reduction
    {n : Nat}
    (hn : 2 < n) :
    ExponentReduces n := by
  have hn1 : 1 < n := Nat.lt_trans (by decide : 1 < 2) hn
  rcases MCore.primeDivisorProperty_proved n hn1 with ⟨p, hp, hpn⟩
  by_cases hp2 : p = 2
  · subst p
    rcases hpn with ⟨k, hk⟩
    have hk1 : 1 < k := two_factor_gt_one hk hn
    rcases MCore.primeDivisorProperty_proved k hk1 with ⟨q, hq, hqk⟩
    by_cases hq2 : q = 2
    · subst q
      rcases hqk with ⟨m, hkm⟩
      refine ⟨4, m, ?_, ?_⟩
      · calc
          n = 2 * k := hk
          _ = 2 * (2 * m) := congrArg (fun t : Nat => 2 * t) hkm
          _ = 4 * m := by omega
      · exact ⟨by decide, Or.inl rfl⟩
    · have h2le : 2 ≤ q := Nat.succ_le_of_lt hq.1
      have h2lt : 2 < q := Nat.lt_of_le_of_ne h2le (Ne.symm hq2)
      have hkn : k ∣ n := by
        refine ⟨2, ?_⟩
        omega
      have hqn : q ∣ n := MCore.nat_dvd_trans hqk hkn
      rcases hqn with ⟨m, hnm⟩
      exact ⟨q, m, hnm, h2lt, Or.inr hq⟩
  · have h2le : 2 ≤ p := Nat.succ_le_of_lt hp.1
    have h2lt : 2 < p := Nat.lt_of_le_of_ne h2le (Ne.symm hp2)
    rcases hpn with ⟨k, hnk⟩
    exact ⟨p, k, hnk, h2lt, Or.inr hp⟩

/-- All three exponents of every Beal datum reduce constructively. -/
theorem beal_exponents_reduce (d : MCore.BealData) :
    ExponentReduces d.x ∧ ExponentReduces d.y ∧ ExponentReduces d.z := by
  exact ⟨exponent_reduction d.x_gt_two,
    exponent_reduction d.y_gt_two,
    exponent_reduction d.z_gt_two⟩

/-- In particular this pressure applies to every primitive Q10 candidate. -/
theorem primitive_exponents_reduce
    (d : MCore.BealData)
    (_hd : PrimitiveBealSolution d) :
    ExponentReduces d.x ∧ ExponentReduces d.y ∧ ExponentReduces d.z :=
  beal_exponents_reduce d

#print axioms MCore.OpenMath.BealQ10.exponent_reduction
#print axioms MCore.OpenMath.BealQ10.primitive_exponents_reduce

end MCore.OpenMath.BealQ10
