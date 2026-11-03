import MCore.BealQuarticPrimeSupport

namespace MCore

/--
On x=z=4, no odd prime divides both c-a and c^2+a^2.
-/
theorem T59_xz_four_sub_quadratic_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c - d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2) := by
  intro h
  rcases h with ⟨hsub, hquad⟩
  have hac_lt : d.a < d.c := by
    have heq' : d.b ^ d.y + d.a ^ d.x = d.c ^ d.z := by
      simpa [Nat.add_comm] using d.equation
    exact T21_right_same_exponent_gap d.b_pos heq' (by simpa [hx, hz])
  have hac : d.a ≤ d.c := Nat.le_of_lt hac_lt
  have hca : p ∣ d.c - d.a := hsub
  have hca2 : p ∣ (d.c - d.a) * (d.c + d.a) :=
    T32_dvd_mul_of_dvd_left hca
  have hdiffsq : (d.c - d.a) * (d.c + d.a) = d.c ^ 2 - d.a ^ 2 := by
    omega
  have hdiffsq' : p ∣ d.c ^ 2 - d.a ^ 2 := by
    simpa [hdiffsq] using hca2
  have h2a2 : p ∣ 2 * (d.a ^ 2) := by
    have hsum :
        p ∣ (d.c ^ 2 + d.a ^ 2) - (d.c ^ 2 - d.a ^ 2) :=
      Nat.dvd_sub hquad hdiffsq'
    have hid :
        (d.c ^ 2 + d.a ^ 2) - (d.c ^ 2 - d.a ^ 2) =
          2 * (d.a ^ 2) := by
      omega
    simpa [hid] using hsum
  have ha2 : p ∣ d.a ^ 2 := by
    rcases T29_prime_dvd_mul hp h2a2 with htwo | ha2
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact False.elim (hp2 heq)
    · exact ha2
  have hpa : p ∣ d.a :=
    T30_prime_dvd_pow_of_pos hp (by decide : 0 < (2 : Nat)) ha2
  have hpc : p ∣ d.c := by
    have hsum : p ∣ (d.c - d.a) + d.a :=
      T11_dvd_add hsub hpa
    simpa [Nat.sub_add_cancel hac] using hsum
  exact d.pairwisePrimitive.2.1 ⟨p, hp.1, hpa, hpc⟩

/--
On x=z=4, no odd prime divides both c+a and c^2+a^2.
-/
theorem T59_xz_four_add_quadratic_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c + d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2) := by
  intro h
  rcases h with ⟨hadd, hquad⟩
  have hsq :
      p ∣ (d.c + d.a) * (d.c + d.a) :=
    T32_dvd_mul_of_dvd_left hadd
  have hsumSq :
      (d.c + d.a) * (d.c + d.a) =
        d.c ^ 2 + 2 * d.c * d.a + d.a ^ 2 := by
    ring
  have hfull :
      p ∣ d.c ^ 2 + 2 * d.c * d.a + d.a ^ 2 := by
    simpa [hsumSq] using hsq
  have h2ca :
      p ∣ 2 * d.c * d.a := by
    have hsub :
        p ∣
          (d.c ^ 2 + 2 * d.c * d.a + d.a ^ 2) -
            (d.c ^ 2 + d.a ^ 2) :=
      Nat.dvd_sub hfull hquad
    have hid :
        (d.c ^ 2 + 2 * d.c * d.a + d.a ^ 2) -
            (d.c ^ 2 + d.a ^ 2) =
          2 * d.c * d.a := by
      omega
    simpa [hid] using hsub
  rcases T29_prime_dvd_mul hp h2ca with h2c | hpa
  · rcases T29_prime_dvd_mul hp h2c with htwo | hpc
    · have hle : p ≤ 2 :=
        Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact hp2 heq
    ·
      have hpa' : p ∣ d.a := by
        have hsub : p ∣ (d.c + d.a) - d.c :=
          Nat.dvd_sub hadd hpc
        simpa using hsub
      exact d.pairwisePrimitive.2.1 ⟨p, hp.1, hpa', hpc⟩
  ·
    have hpc : p ∣ d.c := by
      have hsub : p ∣ (d.c + d.a) - d.a :=
        Nat.dvd_sub hadd hpa
      simpa using hsub
    exact d.pairwisePrimitive.2.1 ⟨p, hp.1, hpa, hpc⟩

/--
Symmetric separation on y=z=4.
-/
theorem T59_yz_four_sub_quadratic_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c - d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2) := by
  intro h
  rcases h with ⟨hsub, hquad⟩
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hbc : d.b ≤ d.c := Nat.le_of_lt hbc_lt
  have hcb2 : p ∣ (d.c - d.b) * (d.c + d.b) :=
    T32_dvd_mul_of_dvd_left hsub
  have hdiffsq : (d.c - d.b) * (d.c + d.b) = d.c ^ 2 - d.b ^ 2 := by
    omega
  have hdiffsq' : p ∣ d.c ^ 2 - d.b ^ 2 := by
    simpa [hdiffsq] using hcb2
  have h2b2 : p ∣ 2 * (d.b ^ 2) := by
    have hsum :
        p ∣ (d.c ^ 2 + d.b ^ 2) - (d.c ^ 2 - d.b ^ 2) :=
      Nat.dvd_sub hquad hdiffsq'
    have hid :
        (d.c ^ 2 + d.b ^ 2) - (d.c ^ 2 - d.b ^ 2) =
          2 * (d.b ^ 2) := by
      omega
    simpa [hid] using hsum
  have hb2 : p ∣ d.b ^ 2 := by
    rcases T29_prime_dvd_mul hp h2b2 with htwo | hb2
    · have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact False.elim (hp2 heq)
    · exact hb2
  have hpb : p ∣ d.b :=
    T30_prime_dvd_pow_of_pos hp (by decide : 0 < (2 : Nat)) hb2
  have hpc : p ∣ d.c := by
    have hsum : p ∣ (d.c - d.b) + d.b :=
      T11_dvd_add hsub hpb
    simpa [Nat.sub_add_cancel hbc] using hsum
  exact d.pairwisePrimitive.2.2 ⟨p, hp.1, hpb, hpc⟩

/--
On y=z=4, no odd prime divides both c+b and c^2+b^2.
-/
theorem T59_yz_four_add_quadratic_odd_prime_disjoint
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {p : Nat}
    (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ (p ∣ d.c + d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2) := by
  intro h
  rcases h with ⟨hadd, hquad⟩
  have hsq :
      p ∣ (d.c + d.b) * (d.c + d.b) :=
    T32_dvd_mul_of_dvd_left hadd
  have hsumSq :
      (d.c + d.b) * (d.c + d.b) =
        d.c ^ 2 + 2 * d.c * d.b + d.b ^ 2 := by
    ring
  have hfull :
      p ∣ d.c ^ 2 + 2 * d.c * d.b + d.b ^ 2 := by
    simpa [hsumSq] using hsq
  have h2cb :
      p ∣ 2 * d.c * d.b := by
    have hsub :
        p ∣
          (d.c ^ 2 + 2 * d.c * d.b + d.b ^ 2) -
            (d.c ^ 2 + d.b ^ 2) :=
      Nat.dvd_sub hfull hquad
    have hid :
        (d.c ^ 2 + 2 * d.c * d.b + d.b ^ 2) -
            (d.c ^ 2 + d.b ^ 2) =
          2 * d.c * d.b := by
      omega
    simpa [hid] using hsub
  rcases T29_prime_dvd_mul hp h2cb with h2c | hpb
  · rcases T29_prime_dvd_mul hp h2c with htwo | hpc
    · have hle : p ≤ 2 :=
        Nat.le_of_dvd (by decide : 0 < (2 : Nat)) htwo
      have heq : p = 2 := Nat.le_antisymm hle hp.two_le
      exact hp2 heq
    ·
      have hpb' : p ∣ d.b := by
        have hsub : p ∣ (d.c + d.b) - d.c :=
          Nat.dvd_sub hadd hpc
        simpa using hsub
      exact d.pairwisePrimitive.2.2 ⟨p, hp.1, hpb', hpc⟩
  ·
    have hpc : p ∣ d.c := by
      have hsub : p ∣ (d.c + d.b) - d.b :=
        Nat.dvd_sub hadd hpb
      simpa using hsub
    exact d.pairwisePrimitive.2.2 ⟨p, hp.1, hpb, hpc⟩

/--
Three-block odd-prime separation packet for quartic residuals.
-/
structure T59QuarticThreeBlockSeparation
    (d : T59ResidualCandidate) : Prop where
  xz_sub_add :
    d.x = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.a ∧ p ∣ d.c + d.a)
  xz_sub_quad :
    d.x = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2)
  xz_add_quad :
    d.x = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c + d.a ∧ p ∣ d.c ^ 2 + d.a ^ 2)
  yz_sub_add :
    d.y = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.b ∧ p ∣ d.c + d.b)
  yz_sub_quad :
    d.y = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c - d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2)
  yz_add_quad :
    d.y = 4 -> d.z = 4 ->
    ∀ p, IsPrime p -> p ≠ 2 ->
      ¬ (p ∣ d.c + d.b ∧ p ∣ d.c ^ 2 + d.b ^ 2)

#print axioms MCore.T59_xz_four_sub_quadratic_odd_prime_disjoint
#print axioms MCore.T59_xz_four_add_quadratic_odd_prime_disjoint
#print axioms MCore.T59_yz_four_sub_quadratic_odd_prime_disjoint
#print axioms MCore.T59_yz_four_add_quadratic_odd_prime_disjoint

end MCore
