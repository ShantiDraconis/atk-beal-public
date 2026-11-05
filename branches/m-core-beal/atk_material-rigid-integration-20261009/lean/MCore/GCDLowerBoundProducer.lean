import MCore.K10

namespace MCore

/-- On the positive Beal domain, a nontrivial common divisor is exactly the
single scalar inequality `1 < gcd(a, gcd(b,c))`. -/
theorem commonDivisor_iff_one_lt_nestedGCD (d : BealData) :
    (∃ q : Nat, CommonDivisor q d.a d.b d.c) ↔
      1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by
  constructor
  · rintro ⟨q, hq, hqa, hqb, hqc⟩
    have hqbc : q ∣ Nat.gcd d.b d.c := Nat.dvd_gcd hqb hqc
    have hqg : q ∣ Nat.gcd d.a (Nat.gcd d.b d.c) :=
      Nat.dvd_gcd hqa hqbc
    have hgpos : 0 < Nat.gcd d.a (Nat.gcd d.b d.c) :=
      Nat.gcd_pos_of_pos_left _ d.a_pos
    exact Nat.lt_of_lt_of_le hq (Nat.le_of_dvd hgpos hqg)
  · intro hg
    let g := Nat.gcd d.a (Nat.gcd d.b d.c)
    refine ⟨g, hg, Nat.gcd_dvd_left _ _, ?_, ?_⟩
    · exact nat_dvd_trans
        (Nat.gcd_dvd_right d.a (Nat.gcd d.b d.c))
        (Nat.gcd_dvd_left d.b d.c)
    · exact nat_dvd_trans
        (Nat.gcd_dvd_right d.a (Nat.gcd d.b d.c))
        (Nat.gcd_dvd_right d.b d.c)

/-- Common-prime and the nested-GCD inequality are therefore equivalent on
every admissible Beal datum. -/
theorem commonPrime_iff_one_lt_nestedGCD (d : BealData) :
    CommonPrime d.a d.b d.c ↔
      1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by
  rw [commonPrime_iff_commonDivisor, commonDivisor_iff_one_lt_nestedGCD]

/-- The smallest scalar producer currently exposed by the arithmetic kernel. -/
def GCDLowerBoundProducer : Prop :=
  ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)

theorem bealConjecture_iff_gcdLowerBoundProducer :
    BealConjecture ↔ GCDLowerBoundProducer := by
  constructor
  · intro h d
    exact (commonPrime_iff_one_lt_nestedGCD d).mp (h d)
  · intro h d
    exact (commonPrime_iff_one_lt_nestedGCD d).mpr (h d)

#print axioms MCore.commonDivisor_iff_one_lt_nestedGCD
#print axioms MCore.commonPrime_iff_one_lt_nestedGCD
#print axioms MCore.bealConjecture_iff_gcdLowerBoundProducer

end MCore
