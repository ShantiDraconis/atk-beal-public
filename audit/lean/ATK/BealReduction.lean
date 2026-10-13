import Mathlib
import ATK.Exact

/-!
# ATK — Beal: redução dos expoentes

Redução certificada: basta provar Beal para expoentes **4 ou primos ímpares**
(`beal_iff_reduced`). Motivo: todo expoente `e > 2` tem um divisor `d` que é 4 ou primo ímpar
(`exists_reduced_dvd`); então `Aᵉ = (A^{e/d})^d`, e um primo que divide `A^{e/d}`, `B^{…}`, `C^{…}`
divide `A`, `B`, `C`.

Forma da solução depois da redução: para cada terna `(p, q, r)` com entradas em `{4, 3, 5, 7, …}`,
mostrar que `aᵖ + bᵠ = cʳ` não tem solução com `gcd = 1`. Casos conhecidos na literatura (não
formalizados aqui): `p = q = r` (Fermat–Wiles), `(n,n,3)` (Darmon–Merel), e — para cada terna
fixa — só finitas soluções primitivas (Darmon–Granville). O caso geral, com expoentes distintos
arbitrários, é o que está em aberto.
-/

namespace ATK.BealReduction

/-- Expoente reduzido: 4 ou primo ímpar. -/
def ReducedExp (e : ℕ) : Prop := e = 4 ∨ (Nat.Prime e ∧ e ≠ 2)

theorem reducedExp_gt_two {e : ℕ} (h : ReducedExp e) : 2 < e := by
  rcases h with rfl | ⟨hp, h2⟩
  · norm_num
  · have := hp.two_le
    omega

/-- Todo expoente `> 2` tem um divisor reduzido. -/
theorem exists_reduced_dvd {e : ℕ} (he : 2 < e) : ∃ d, ReducedExp d ∧ d ∣ e := by
  by_cases h4 : 4 ∣ e
  · exact ⟨4, Or.inl rfl, h4⟩
  · by_cases hodd : e % 2 = 1
    · have hne : e ≠ 1 := by omega
      refine ⟨e.minFac, Or.inr ⟨Nat.minFac_prime hne, ?_⟩, Nat.minFac_dvd e⟩
      intro h2
      have h := Nat.minFac_dvd e
      rw [h2] at h
      omega
    · obtain ⟨m, rfl⟩ : 2 ∣ e := Nat.dvd_of_mod_eq_zero (by omega)
      have hm1 : m ≠ 1 := by omega
      refine ⟨m.minFac, Or.inr ⟨Nat.minFac_prime hm1, ?_⟩,
        (Nat.minFac_dvd m).trans (dvd_mul_left m 2)⟩
      intro h2
      have h := Nat.minFac_dvd m
      rw [h2] at h
      omega

/-- Beal restrito a expoentes reduzidos. -/
def BealReduced : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → ReducedExp x → ReducedExp y → ReducedExp z →
    A ^ x + B ^ y = C ^ z → 1 < Nat.gcd A (Nat.gcd B C)

/-- **Redução certificada**: Beal ⇔ Beal com expoentes 4 ou primos ímpares. -/
theorem beal_iff_reduced : ATK.Exact.Beal ↔ BealReduced := by
  constructor
  · intro h A B C x y z hA hB hC hx hy hz heq
    exact h A B C x y z hA hB hC (reducedExp_gt_two hx) (reducedExp_gt_two hy)
      (reducedExp_gt_two hz) heq
  · intro h
    show ATK.BealDescent.BealStatement
    intro A B C x y z hA hB hC hx hy hz heq
    obtain ⟨a, ha, a', rfl⟩ := exists_reduced_dvd hx
    obtain ⟨b, hb, b', rfl⟩ := exists_reduced_dvd hy
    obtain ⟨c, hc, c', rfl⟩ := exists_reduced_dvd hz
    have heq' : (A ^ a') ^ a + (B ^ b') ^ b = (C ^ c') ^ c := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm a' a, mul_comm b' b, mul_comm c' c]
      exact heq
    have hg := h (A ^ a') (B ^ b') (C ^ c') a b c (pow_pos hA _) (pow_pos hB _) (pow_pos hC _)
      ha hb hc heq'
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd
      (by omega : Nat.gcd (A ^ a') (Nat.gcd (B ^ b') (C ^ c')) ≠ 1)
    have hpA : p ∣ A := hp.dvd_of_dvd_pow (hpg.trans (Nat.gcd_dvd_left _ _))
    have hpB : p ∣ B :=
      hp.dvd_of_dvd_pow ((hpg.trans (Nat.gcd_dvd_right _ _)).trans (Nat.gcd_dvd_left _ _))
    have hpC : p ∣ C :=
      hp.dvd_of_dvd_pow ((hpg.trans (Nat.gcd_dvd_right _ _)).trans (Nat.gcd_dvd_right _ _))
    have hdvd : p ∣ Nat.gcd A (Nat.gcd B C) := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
    have hpos : 0 < Nat.gcd A (Nat.gcd B C) := Nat.gcd_pos_of_pos_left _ hA
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd)

end ATK.BealReduction

#print axioms ATK.BealReduction.reducedExp_gt_two
#print axioms ATK.BealReduction.exists_reduced_dvd
#print axioms ATK.BealReduction.beal_iff_reduced
