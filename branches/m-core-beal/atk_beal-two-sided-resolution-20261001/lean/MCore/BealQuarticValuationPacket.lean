import MCore.BealQuarticValuationLaw

namespace MCore

theorem T59_yz_four_sub_factorization_multiple
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqsub : q ∣ d.c - d.b) :
    d.x ∣ (d.c - d.b).factorization q := by
  have hfac := T59_yz_four_exact_factorization d hy hz
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hA0 : d.c - d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hbc_lt)
  have hB0 : d.c + d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.b_pos)
  have hC0 : d.c ^ 2 + d.b ^ 2 ≠ 0 := by
    have hb2 : 0 < d.b ^ 2 := Nat.pow_pos d.b_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ hb2)
  have ha0 : d.a ≠ 0 := Nat.ne_of_gt d.a_pos
  have hqB : ¬ q ∣ d.c + d.b := by
    intro h
    exact T59_yz_four_linear_factors_odd_prime_disjoint
      d hy hz hq hq2 ⟨hqsub, h⟩
  have hqC : ¬ q ∣ d.c ^ 2 + d.b ^ 2 := by
    intro h
    exact T59_yz_four_sub_quadratic_odd_prime_disjoint
      d hy hz hq hq2 ⟨hqsub, h⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 ha0 hfac hqB hqC

theorem T59_yz_four_add_factorization_multiple
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqadd : q ∣ d.c + d.b) :
    d.x ∣ (d.c + d.b).factorization q := by
  have hfac0 := T59_yz_four_exact_factorization d hy hz
  have hfac :
      d.a ^ d.x =
        (d.c + d.b) * ((d.c - d.b) * (d.c ^ 2 + d.b ^ 2)) := by
    calc
      d.a ^ d.x =
          (d.c - d.b) * ((d.c + d.b) * (d.c ^ 2 + d.b ^ 2)) := hfac0
      _ = (d.c + d.b) * ((d.c - d.b) * (d.c ^ 2 + d.b ^ 2)) := by
        ring
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hA0 : d.c + d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.b_pos)
  have hB0 : d.c - d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hbc_lt)
  have hC0 : d.c ^ 2 + d.b ^ 2 ≠ 0 := by
    have hb2 : 0 < d.b ^ 2 := Nat.pow_pos d.b_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ hb2)
  have ha0 : d.a ≠ 0 := Nat.ne_of_gt d.a_pos
  have hqB : ¬ q ∣ d.c - d.b := by
    intro h
    exact T59_yz_four_linear_factors_odd_prime_disjoint
      d hy hz hq hq2 ⟨h, hqadd⟩
  have hqC : ¬ q ∣ d.c ^ 2 + d.b ^ 2 := by
    intro h
    exact T59_yz_four_add_quadratic_odd_prime_disjoint
      d hy hz hq hq2 ⟨hqadd, h⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 ha0 hfac hqB hqC

theorem T59_yz_four_quad_factorization_multiple
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4)
    {q : Nat}
    (hq : IsPrime q)
    (hq2 : q ≠ 2)
    (hqquad : q ∣ d.c ^ 2 + d.b ^ 2) :
    d.x ∣ (d.c ^ 2 + d.b ^ 2).factorization q := by
  have hfac0 := T59_yz_four_exact_factorization d hy hz
  have hfac :
      d.a ^ d.x =
        (d.c ^ 2 + d.b ^ 2) * ((d.c - d.b) * (d.c + d.b)) := by
    calc
      d.a ^ d.x =
          (d.c - d.b) * ((d.c + d.b) * (d.c ^ 2 + d.b ^ 2)) := hfac0
      _ = (d.c ^ 2 + d.b ^ 2) * ((d.c - d.b) * (d.c + d.b)) := by
        ring
  have hbc_lt : d.b < d.c :=
    T21_right_same_exponent_gap d.a_pos d.equation (by simpa [hy, hz])
  have hA0 : d.c ^ 2 + d.b ^ 2 ≠ 0 := by
    have hb2 : 0 < d.b ^ 2 := Nat.pow_pos d.b_pos
    exact Nat.ne_of_gt (Nat.add_pos_right _ hb2)
  have hB0 : d.c - d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_sub_of_lt hbc_lt)
  have hC0 : d.c + d.b ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_left d.c d.b_pos)
  have ha0 : d.a ≠ 0 := Nat.ne_of_gt d.a_pos
  have hqB : ¬ q ∣ d.c - d.b := by
    intro h
    exact T59_yz_four_sub_quadratic_odd_prime_disjoint
      d hy hz hq hq2 ⟨h, hqquad⟩
  have hqC : ¬ q ∣ d.c + d.b := by
    intro h
    exact T59_yz_four_add_quadratic_odd_prime_disjoint
      d hy hz hq hq2 ⟨h, hqquad⟩
  exact exponent_dvd_isolated_factor_factorization
    hA0 hB0 hC0 ha0 hfac hqB hqC

structure T59QuarticValuationPacket
    (d : T59ResidualCandidate) : Prop where
  xz_sub :
    d.x = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c - d.a ->
      d.y ∣ (d.c - d.a).factorization q
  xz_add :
    d.x = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c + d.a ->
      d.y ∣ (d.c + d.a).factorization q
  xz_quad :
    d.x = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c ^ 2 + d.a ^ 2 ->
      d.y ∣ (d.c ^ 2 + d.a ^ 2).factorization q
  yz_sub :
    d.y = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c - d.b ->
      d.x ∣ (d.c - d.b).factorization q
  yz_add :
    d.y = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c + d.b ->
      d.x ∣ (d.c + d.b).factorization q
  yz_quad :
    d.y = 4 -> d.z = 4 ->
    ∀ q, IsPrime q -> q ≠ 2 -> q ∣ d.c ^ 2 + d.b ^ 2 ->
      d.x ∣ (d.c ^ 2 + d.b ^ 2).factorization q

def T59_quartic_valuation_packet
    (d : T59ResidualCandidate) :
    T59QuarticValuationPacket d where
  xz_sub := fun hx hz q hq hq2 h =>
    T59_xz_four_sub_factorization_multiple d hx hz hq hq2 h
  xz_add := fun hx hz q hq hq2 h =>
    T59_xz_four_add_factorization_multiple d hx hz hq hq2 h
  xz_quad := fun hx hz q hq hq2 h =>
    T59_xz_four_quad_factorization_multiple d hx hz hq hq2 h
  yz_sub := fun hy hz q hq hq2 h =>
    T59_yz_four_sub_factorization_multiple d hy hz hq hq2 h
  yz_add := fun hy hz q hq hq2 h =>
    T59_yz_four_add_factorization_multiple d hy hz hq hq2 h
  yz_quad := fun hy hz q hq hq2 h =>
    T59_yz_four_quad_factorization_multiple d hy hz hq hq2 h

#print axioms MCore.T59_yz_four_sub_factorization_multiple
#print axioms MCore.T59_yz_four_add_factorization_multiple
#print axioms MCore.T59_yz_four_quad_factorization_multiple
#print axioms MCore.T59_quartic_valuation_packet

end MCore
