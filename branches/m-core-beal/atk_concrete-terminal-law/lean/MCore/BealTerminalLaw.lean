import MCore.GCDLowerBoundProducer
import MCore.BealDirectProducer

namespace MCore

/-!
# Concrete Beal terminal law

This file identifies the exact certification and refutation predicates already
present in this repository. No new arithmetic hypothesis is introduced.
-/

/-- The concrete scalar defect on an admissible Beal datum. -/
def BealGCDDefect (d : BealData) : Nat :=
  Nat.gcd d.a (Nat.gcd d.b d.c) - 1

/-- Certification is exactly the existing Beal conjecture. -/
def BealTerminalCertifies : Prop :=
  BealConjecture

/-- Refutation is the existence of one admissible primitive solution. -/
def BealTerminalRefutes : Prop :=
  ∃ d : BealData, Nat.gcd d.a (Nat.gcd d.b d.c) ≤ 1

theorem beal_terminal_certifies_iff_gcdLowerBound :
    BealTerminalCertifies ↔ GCDLowerBoundProducer := by
  exact bealConjecture_iff_gcdLowerBoundProducer

theorem beal_terminal_refutes_iff_counterexample :
    BealTerminalRefutes ↔ ∃ d : BealData, BealCounterexample d := by
  simp only [BealTerminalRefutes, BealCounterexample]
  constructor
  · rintro ⟨d, hg⟩
    refine ⟨d, ?_⟩
    intro hprime
    have hgt := (commonPrime_iff_one_lt_nestedGCD d).mp hprime
    exact (Nat.not_lt_of_ge hg) hgt
  · rintro ⟨d, hcounter⟩
    refine ⟨d, ?_⟩
    have hnot : ¬ 1 < Nat.gcd d.a (Nat.gcd d.b d.c) := by
      intro hgt
      exact hcounter ((commonPrime_iff_one_lt_nestedGCD d).mpr hgt)
    exact Nat.le_of_not_gt hnot

theorem not_beal_terminal_certifies_iff_refutes :
    ¬ BealTerminalCertifies ↔ BealTerminalRefutes := by
  constructor
  · intro h
    have hnot : ¬ GCDLowerBoundProducer := by
      intro hg
      exact h ((bealConjecture_iff_gcdLowerBoundProducer).2 hg)
    simpa [GCDLowerBoundProducer, BealTerminalRefutes] using hnot
  · intro href hcert
    have hg : GCDLowerBoundProducer :=
      (bealConjecture_iff_gcdLowerBoundProducer).1 hcert
    rcases href with ⟨d, hle⟩
    exact (Nat.not_lt_of_ge hle) (hg d)

theorem beal_terminal_cert_refute_disjoint :
    ¬ (BealTerminalCertifies ∧ BealTerminalRefutes) := by
  rintro ⟨hcert, href⟩
  exact (not_beal_terminal_certifies_iff_refutes.2 href) hcert

#print axioms MCore.beal_terminal_certifies_iff_gcdLowerBound
#print axioms MCore.beal_terminal_refutes_iff_counterexample
#print axioms MCore.not_beal_terminal_certifies_iff_refutes
#print axioms MCore.beal_terminal_cert_refute_disjoint

end MCore
