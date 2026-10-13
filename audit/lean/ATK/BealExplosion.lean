import Mathlib
import ATK.Exact

/-!
# ATK — Linha de explosão para Beal

Adaptação da linha de explosão do NS (testemunha / refutação / dicotomia):

* **testemunha de explosão** `ATK.BealDescent.PrimitiveSolution`: `Aˣ + Bʸ = Cᶻ`, `x, y, z > 2`,
  `gcd(A, B, C) = 1` — um certificado FINITO;
* **refutação** `explosion_refutes : PrimitiveSolution → ¬ ATK.Exact.Beal`; e
  `refute_of_numbers`: basta verificar a aritmética de números explícitos;
* **dicotomia** `beal_iff_no_explosion : Beal ↔ IsEmpty PrimitiveSolution`;
* **obstrução por descida** (o mecanismo do programa): `descent_iff_no_explosion` — uma descida
  bem-fundada (`WFDescent`: toda solução primitiva gera outra estritamente menor) existe ⇔ não há
  explosão. A descida infinita é a "explosão impossível".
* **fronteira** `boundary_explosion`: com expoentes 2 a explosão existe (`3² + 4² = 5²`, `gcd = 1`).
-/

namespace ATK.BealExplosion

open ATK.BealDescent

theorem explosion_refutes (w : PrimitiveSolution) : ¬ ATK.Exact.Beal := by
  intro h
  have hg := h w.A w.B w.C w.x w.y w.z w.hA w.hB w.hC w.hx w.hy w.hz w.equation
  rw [w.coprime] at hg
  exact lt_irrefl 1 hg

/-- Dicotomia: Beal ⇔ não existe explosão (solução primitiva). -/
theorem beal_iff_no_explosion : ATK.Exact.Beal ↔ IsEmpty PrimitiveSolution := by
  constructor
  · intro h
    exact ⟨fun w => explosion_refutes w h⟩
  · intro h
    show BealStatement
    intro A B C x y z hA hB hC hx hy hz heq
    by_contra hle
    push_neg at hle
    have hpos : 0 < Nat.gcd A (Nat.gcd B C) := Nat.gcd_pos_of_pos_left _ hA
    exact h.1 ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, by omega⟩

/-- Obstrução por descida infinita ⇔ ausência de explosão. -/
theorem descent_iff_no_explosion : Nonempty WFDescent ↔ IsEmpty PrimitiveSolution :=
  descent_iff_beal.trans beal_iff_no_explosion

/-- Certificado finito: uma testemunha numérica explícita refuta Beal. -/
theorem refute_of_numbers (A B C x y z : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) (heq : A ^ x + B ^ y = C ^ z)
    (hg : Nat.gcd A (Nat.gcd B C) = 1) : ¬ ATK.Exact.Beal :=
  explosion_refutes ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, hg⟩

/-- Fronteira: com expoentes 2 a explosão existe. -/
theorem boundary_explosion : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 ∧ Nat.gcd 3 (Nat.gcd 4 5) = 1 := by
  norm_num

end ATK.BealExplosion

#print axioms ATK.BealExplosion.explosion_refutes
#print axioms ATK.BealExplosion.beal_iff_no_explosion
#print axioms ATK.BealExplosion.descent_iff_no_explosion
#print axioms ATK.BealExplosion.refute_of_numbers
#print axioms ATK.BealExplosion.boundary_explosion
