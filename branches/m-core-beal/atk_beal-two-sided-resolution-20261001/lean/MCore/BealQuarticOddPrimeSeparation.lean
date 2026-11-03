import MCore.BealQuarticFactorization

namespace MCore

/--
On the x=z=4 residual branch, no odd prime can divide both linear quartic
factors c-a and c+a. Such a prime would divide both a and c, contradicting
pairwise primitiveness.
-/
theorem T59_xz_four_linear_factors_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c - d.a ∧ p ∣ d.c + d.a) := by
  intro h
  rcases h with ⟨hminus, hplus⟩
  have hac_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hac : d.a ≤ d.c := Nat.le_of_lt hac_lt
  have h2a : p ∣ 2 * d.a := by
    have hsub : p ∣ (d.c + d.a) - (d.c - d.a) :=
      Nat.dvd_sub hplus hminus
    have hid : (d.c + d.a) - (d.c - d.a) = 2 * d.a := by
      omega
    simpa [hid] using hsub
  have hpa : p ∣ d.a := by
    rcases T29_prime_dvd_mul hp h2a with htwo | ha
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact False.elim (hp2 heq)
    · exact ha
  have hpc : p ∣ d.c := by
    have hsub : p ∣ (d.c + d.a) - d.a :=
      Nat.dvd_sub hplus hpa
    simpa using hsub
  exact d.pairwisePrimitive.2.1 ⟨p, hp.1, hpa, hpc⟩

/--
Symmetric statement on y=z=4: no odd prime divides both c-b and c+b.
-/
theorem T59_yz_four_linear_factors_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c - d.b ∧ p ∣ d.c + d.b) := by
  intro h
  rcases h with ⟨hminus, hplus⟩
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hbc : d.b ≤ d.c := Nat.le_of_lt hbc_lt
  have h2b : p ∣ 2 * d.b := by
    have hsub : p ∣ (d.c + d.b) - (d.c - d.b) :=
      Nat.dvd_sub hplus hminus
    have hid : (d.c + d.b) - (d.c - d.b) = 2 * d.b := by
      omega
    simpa [hid] using hsub
  have hpb : p ∣ d.b := by
    rcases T29_prime_dvd_mul hp h2b with htwo | hb
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact False.elim (hp2 heq)
    · exact hb
  have hpc : p ∣ d.c := by
    have hsub : p ∣ (d.c + d.b) - d.b :=
      Nat.dvd_sub hplus hpb
    simpa using hsub
  exact d.pairwisePrimitive.2.2 ⟨p, hp.1, hpb, hpc⟩

#print axioms MCore.T59_xz_four_linear_factors_odd_prime_disjoint
#print axioms MCore.T59_yz_four_linear_factors_odd_prime_disjoint

end MCore
