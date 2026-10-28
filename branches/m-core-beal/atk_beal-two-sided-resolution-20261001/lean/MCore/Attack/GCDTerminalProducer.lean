import MCore.K10

namespace MCore
namespace Attack

/-- Canonical scalar common-divisor carrier for the three Beal bases. -/
def TripleGCD (a b c : Nat) : Nat :=
  Nat.gcd a (Nat.gcd b c)

/-- Any nontrivial common divisor divides the canonical triple gcd. -/
theorem commonDivisor_dvd_tripleGCD
    {a b c d : Nat}
    (h : CommonDivisor d a b c) :
    d ∣ TripleGCD a b c := by
  rcases h with ⟨_, hda, hdb, hdc⟩
  exact Nat.dvd_gcd hda (Nat.dvd_gcd hdb hdc)

/-- The triple gcd itself divides all three bases. -/
theorem tripleGCD_common_divides
    (a b c : Nat) :
    TripleGCD a b c ∣ a ∧
    TripleGCD a b c ∣ b ∧
    TripleGCD a b c ∣ c := by
  constructor
  · exact Nat.gcd_dvd_left a (Nat.gcd b c)
  constructor
  · exact Nat.dvd_trans (Nat.gcd_dvd_right a (Nat.gcd b c))
      (Nat.gcd_dvd_left b c)
  · exact Nat.dvd_trans (Nat.gcd_dvd_right a (Nat.gcd b c))
      (Nat.gcd_dvd_right b c)

/-- A lower bound on the canonical triple gcd closes the current terminal producer. -/
theorem tripleGCD_gt_one_closes_commonDivisor
    (d : BealData)
    (hgt : 1 < TripleGCD d.a d.b d.c) :
    ∃ q : Nat, CommonDivisor q d.a d.b d.c := by
  refine ⟨TripleGCD d.a d.b d.c, hgt, ?_, ?_, ?_⟩
  · exact (tripleGCD_common_divides d.a d.b d.c).1
  · exact (tripleGCD_common_divides d.a d.b d.c).2.1
  · exact (tripleGCD_common_divides d.a d.b d.c).2.2

def UniversalTripleGCDLowerBound : Prop :=
  ∀ d : BealData, 1 < TripleGCD d.a d.b d.c

theorem universalTripleGCDLowerBound_closes_beal
    (h : UniversalTripleGCDLowerBound) :
    BealConjecture := by
  intro d
  exact (commonPrime_iff_commonDivisor).2
    (tripleGCD_gt_one_closes_commonDivisor d (h d))

def terminalStatus : String :=
  "OPEN_MATH: prove UniversalTripleGCDLowerBound"

#print axioms commonDivisor_dvd_tripleGCD
#print axioms tripleGCD_common_divides
#print axioms tripleGCD_gt_one_closes_commonDivisor
#print axioms universalTripleGCDLowerBound_closes_beal

end Attack
end MCore
