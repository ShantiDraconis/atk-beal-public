import MCore.T59
import MCore.K9

namespace MCore

/-!
B01 conductor-level interface for the mixed-exponent Frey route.

This is structural bookkeeping only. It deliberately carries no modularity,
irreducibility, unramifiedness, or level-lowering theorem.
-/

def B01Squarefree (N : Nat) : Prop :=
  ∀ q : Nat, IsPrime q → ¬ q * q ∣ N

structure B01ConductorLevel (d : T59ResidualCandidate) (N : Nat) : Prop where
  pos : 0 < N
  squarefree : B01Squarefree N
  support :
    ∀ q : Nat, IsPrime q → q ∣ N → q ∣ d.a * d.b * d.c

namespace B01ConductorLevel

variable {d : T59ResidualCandidate} {N M q : Nat}

theorem of_dvd
    (hN : B01ConductorLevel d N)
    (hMN : M ∣ N)
    (hM : 0 < M) :
    B01ConductorLevel d M := by
  refine ⟨hM, ?_, ?_⟩
  · intro p hp hppM
    exact hN.squarefree p hp (MCore.nat_dvd_trans hppM hMN)
  · intro p hp hpM
    exact hN.support p hp (MCore.nat_dvd_trans hpM hMN)

theorem prime_support
    (hN : B01ConductorLevel d N)
    (hq : IsPrime q)
    (hqN : q ∣ N) :
    q ∣ d.a * d.b * d.c :=
  hN.support q hq hqN

theorem prime_square_not_dvd
    (hN : B01ConductorLevel d N)
    (hq : IsPrime q) :
    ¬ q * q ∣ N :=
  hN.squarefree q hq

theorem four_not_dvd
    (hN : B01ConductorLevel d N)
    (h2 : IsPrime 2) :
    ¬ 4 ∣ N := by
  have hsq : (4 : Nat) = 2 * 2 := by decide
  rw [hsq]
  exact hN.prime_square_not_dvd h2

#print axioms MCore.B01ConductorLevel.of_dvd
#print axioms MCore.B01ConductorLevel.prime_support
#print axioms MCore.B01ConductorLevel.prime_square_not_dvd
#print axioms MCore.B01ConductorLevel.four_not_dvd

end B01ConductorLevel
end MCore
