import Mathlib
import ATK.Exact

/-!
# ATK — Beal no regime suave: as versões que JÁ são teoremas

No NS, a alternativa com força (C)/(D) é a versão que fechou. Em Beal, as versões que fecham hoje
no kernel são:

* **Beal sobre polinômios** (análogo de corpo de funções), em característica 0:
  `beal_poly` — se `aˣ + bʸ = cᶻ` com `a, b, c ≠ 0`, `x, y, z > 2` e `a, b` coprimos, então
  `a, b, c` são constantes. Ou seja, toda solução não constante tem fator comum
  (`beal_poly_common_factor`). Usa o teorema de Fermat–Catalan polinomial da Mathlib
  (`Polynomial.flt_catalan`, via Mason–Stothers).
* **Diagonal `x = y = z = n` com `3 ∣ n` ou `4 ∣ n`**: `beal_diagonal` — vale porque não há
  solução alguma (Fermat para 3 e 4 na Mathlib: `fermatLastTheoremThree`, `fermatLastTheoremFour`).

O que NÃO fecha: Beal sobre os inteiros com expoentes arbitrários (o alvo `ATK.Exact.Beal`). A
prova polinomial usa derivadas (Mason–Stothers), que não têm análogo direto nos inteiros: o
análogo inteiro de Mason–Stothers é a conjectura abc.
-/

namespace ATK.BealSmooth

open Polynomial

/-- `y z + z x + x y ≤ x y z` para expoentes `≥ 3` (isto é, `1/x + 1/y + 1/z ≤ 1`). -/
theorem exponent_ineq {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) :
    y * z + z * x + x * y ≤ x * y * z := by
  have h1 := Nat.mul_le_mul_right (y * z) (show 3 ≤ x by omega)
  have h2 := Nat.mul_le_mul_right (z * x) (show 3 ≤ y by omega)
  have h3 := Nat.mul_le_mul_right (x * y) (show 3 ≤ z by omega)
  nlinarith [h1, h2, h3]

/-- **Beal sobre polinômios** (característica 0). -/
theorem beal_poly (k : Type*) [Field k] [CharZero k] :
    ∀ (a b c : k[X]) (x y z : ℕ), a ≠ 0 → b ≠ 0 → c ≠ 0 → 2 < x → 2 < y → 2 < z →
      a ^ x + b ^ y = c ^ z → IsCoprime a b →
        a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  classical
  intro a b c x y z ha hb hc hx hy hz heq hab
  have heq' : C (1 : k) * a ^ x + C 1 * b ^ y + C (-1) * c ^ z = 0 := by
    first
      | rw [map_one, map_neg, map_one, one_mul, one_mul, neg_one_mul, heq, add_neg_cancel]
      | simp [heq]
  exact Polynomial.flt_catalan (p := x) (q := y) (r := z) (by omega) (by omega) (by omega)
    (exponent_ineq hx hy hz)
    (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)) ha hb hc hab one_ne_zero one_ne_zero
    (neg_ne_zero.mpr one_ne_zero) heq'

/-- Forma "fator comum": toda solução com algum termo não constante tem `a, b` não coprimos. -/
theorem beal_poly_common_factor (k : Type*) [Field k] [CharZero k]
    {a b c : k[X]} {x y z : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) (heq : a ^ x + b ^ y = c ^ z)
    (hnc : 0 < a.natDegree ∨ 0 < b.natDegree ∨ 0 < c.natDegree) : ¬ IsCoprime a b := by
  intro hab
  obtain ⟨h1, h2, h3⟩ := beal_poly k a b c x y z ha hb hc hx hy hz heq hab
  omega

/-- **Diagonal**: Beal com `x = y = z = n`, `3 ∣ n` ou `4 ∣ n` (vale sem solução alguma). -/
theorem beal_diagonal : ∀ n : ℕ, (3 ∣ n ∨ 4 ∣ n) → ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
    A ^ n + B ^ n = C ^ n → 1 < Nat.gcd A (Nat.gcd B C) := by
  intro n hn A B C hA hB hC heq
  have hF : FermatLastTheoremFor n := by
    rcases hn with h | h
    · exact FermatLastTheoremFor.mono h fermatLastTheoremThree
    · exact FermatLastTheoremFor.mono h fermatLastTheoremFour
  exact absurd heq (hF A B C hA.ne' hB.ne' hC.ne')

end ATK.BealSmooth

#print axioms ATK.BealSmooth.exponent_ineq
#print axioms ATK.BealSmooth.beal_poly
#print axioms ATK.BealSmooth.beal_poly_common_factor
#print axioms ATK.BealSmooth.beal_diagonal
