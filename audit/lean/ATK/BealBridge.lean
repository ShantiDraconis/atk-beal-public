import Mathlib
import ATK.Exact

/-!
# ATK — Beal: ponte condicional no formato da ponte NS (`clayC_of_fc`)

Estado do NS: alvo exato `ClayC` + hipótese enunciada `FCBreakdownR3` + ponte certificada
`FCBreakdownR3 → ClayC`. Aqui, o mesmo formato para Beal:

* **Alvo exato** (portão ATK): `ATK.Exact.Beal`
  (`∀ A B C x y z, 0<A,B,C → 2<x,y,z → Aˣ+Bʸ=Cᶻ → 1 < gcd(A, gcd(B,C))`).
* **Hipótese H** = o produtor terminal do programa (`m-core-beal`,
  `lean/MCore/GCDLowerBoundProducer.lean`), copiado verbatim abaixo com o tipo `BealData`.
* **Ponte**: `beal_of_producer : GCDLowerBoundProducer → ATK.Exact.Beal`.

Força da hipótese (registrada sem disfarce): `producer_of_beal` prova a recíproca — H é
**equivalente** ao alvo. Diferente do NS, onde H tem prova externa reivindicada, aqui H é o
próprio conteúdo aberto. Também se prova que a especificação do programa (`BealConjecture`,
fator primo comum) é equivalente ao alvo: `bealConjecture_iff_exact`.
-/

namespace ATK.BealBridge

/-- Cópia verbatim de `MCore.BealData` (`BealSpecification.lean`). -/
structure BealData where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_gt_two : 2 < x
  y_gt_two : 2 < y
  z_gt_two : 2 < z
  equation : a ^ x + b ^ y = c ^ z

/-- Cópia verbatim de `MCore.IsPrime`. -/
def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Cópia verbatim de `MCore.CommonPrime`. -/
def CommonPrime (a b c : Nat) : Prop :=
  ∃ p : Nat, IsPrime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- Cópia verbatim de `MCore.BealConjecture`. -/
def BealConjecture : Prop :=
  ∀ d : BealData, CommonPrime d.a d.b d.c

/-- **Hipótese H** — cópia verbatim de `MCore.GCDLowerBoundProducer`. -/
def GCDLowerBoundProducer : Prop :=
  ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)

/-- **Ponte certificada** `H → alvo exato`. -/
theorem beal_of_producer (h : GCDLowerBoundProducer) : ATK.Exact.Beal := by
  show ATK.BealDescent.BealStatement
  intro A B C x y z hA hB hC hx hy hz heq
  exact h ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq⟩

/-- Recíproca: o alvo implica H. Logo H é equivalente ao alvo (força registrada). -/
theorem producer_of_beal (h : ATK.Exact.Beal) : GCDLowerBoundProducer := by
  intro d
  exact h d.a d.b d.c d.x d.y d.z d.a_pos d.b_pos d.c_pos d.x_gt_two d.y_gt_two d.z_gt_two
    d.equation

theorem producer_iff_beal : GCDLowerBoundProducer ↔ ATK.Exact.Beal :=
  ⟨beal_of_producer, producer_of_beal⟩

/-- O primo local do programa coincide com `Nat.Prime`. -/
theorem isPrime_iff (p : Nat) : IsPrime p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨hp, hdiv⟩
    refine Nat.prime_def.mpr ⟨hp, fun m hm => ?_⟩
    exact hdiv m hm
  · intro hp
    exact ⟨hp.one_lt, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/-- Fator primo comum ⇔ `gcd` aninhado maior que 1 (para `a > 0`). -/
theorem commonPrime_iff_gcd {a b c : Nat} (ha : 0 < a) :
    CommonPrime a b c ↔ 1 < Nat.gcd a (Nat.gcd b c) := by
  constructor
  · rintro ⟨p, hp, hpa, hpb, hpc⟩
    have hg : p ∣ Nat.gcd a (Nat.gcd b c) := Nat.dvd_gcd hpa (Nat.dvd_gcd hpb hpc)
    have hpos : 0 < Nat.gcd a (Nat.gcd b c) := Nat.gcd_pos_of_pos_left _ ha
    exact lt_of_lt_of_le hp.1 (Nat.le_of_dvd hpos hg)
  · intro hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd a (Nat.gcd b c) ≠ 1)
    refine ⟨p, (isPrime_iff p).mpr hp, ?_, ?_, ?_⟩
    · exact hpg.trans (Nat.gcd_dvd_left _ _)
    · exact (hpg.trans (Nat.gcd_dvd_right _ _)).trans (Nat.gcd_dvd_left _ _)
    · exact (hpg.trans (Nat.gcd_dvd_right _ _)).trans (Nat.gcd_dvd_right _ _)

/-- A especificação do programa é exatamente o alvo do portão. -/
theorem bealConjecture_iff_exact : BealConjecture ↔ ATK.Exact.Beal := by
  rw [← producer_iff_beal]
  constructor
  · intro h d
    exact (commonPrime_iff_gcd d.a_pos).mp (h d)
  · intro h d
    exact (commonPrime_iff_gcd d.a_pos).mpr (h d)

/-- Falsificador: um dado de Beal com `gcd = 1` refuta H (e, pela ponte, o alvo). -/
theorem producer_refuted_by (d : BealData) (hd : Nat.gcd d.a (Nat.gcd d.b d.c) = 1) :
    ¬ GCDLowerBoundProducer := by
  intro h
  have := h d
  omega

end ATK.BealBridge

#print axioms ATK.BealBridge.beal_of_producer
#print axioms ATK.BealBridge.producer_of_beal
#print axioms ATK.BealBridge.producer_iff_beal
#print axioms ATK.BealBridge.isPrime_iff
#print axioms ATK.BealBridge.commonPrime_iff_gcd
#print axioms ATK.BealBridge.bealConjecture_iff_exact
#print axioms ATK.BealBridge.producer_refuted_by
