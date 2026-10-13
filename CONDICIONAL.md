# Estado: CONDICIONAL — Conjectura de Beal

Auditoria de 13/10/2026 sobre o commit `776d2e6` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 0. Ponte no formato NS — certificada no kernel

Mesmo formato do Navier–Stokes (`clayC_of_fc : FCBreakdownR3 → ClayC`):

| Peça | Declaração (`audit/lean/ATK/BealBridge.lean`) |
|---|---|
| Alvo exato | `ATK.Exact.Beal` |
| Hipótese H | `ATK.BealBridge.GCDLowerBoundProducer` — cópia verbatim do produtor do programa |
| Ponte | `beal_of_producer : GCDLowerBoundProducer → ATK.Exact.Beal` |
| Força de H | **equivalente** ao alvo (`producer_iff_beal`); a especificação do programa também (`bealConjecture_iff_exact`) |
| Falsificador de H | `producer_refuted_by`: um dado de Beal com `gcd = 1` |
| Kernel | **7/7 CERTIFIED** — Lean 4.34.1 + Mathlib v4.34.1, só `propext`/`Classical.choice`/`Quot.sound` (workflow `audit-kernel`) |

Nota: Beal **não** é um dos 7 problemas do Milênio; o prêmio é da AMS (Beal Prize), com regras
próprias de publicação e aceitação.

## 1. Alvo exato

Se `a^x + b^y = c^z` com `a, b, c ≥ 1` e `x, y, z > 2`, então `a`, `b`, `c` têm fator primo comum.

`MCore.BealConjecture` (`BealSpecification.lean`) foi conferido linha a linha e **é exatamente
esse enunciado** (com `IsPrime` local correto: `1 < p` e só os divisores triviais). No portão ATK
o alvo é `ATK.Exact.Beal` (ou `¬ ATK.Exact.Beal`).

**Estado no portão: CONDICIONAL** — ponte certificada; H em aberto (equivalente ao alvo).

## 2. Varredura do conteúdo

14 arquivos Lean · 0 `axiom` · 0 `sorry`/`admit`. Os nós K3–K7 se declaram `openBridge` e provam
que não podem ser promovidos (`k3_gap_not_certified`, `k5_openBridge_cannot_certify`,
`k7_endpoint_not_certified`) — correto.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Natureza | Por que é condicional | O que fechar |
|---|---|---|---|---|
| B1 | `GCDLowerBoundProducer` / `CommonDivisorProducer` (`∀ d : BealData, 1 < gcd a (gcd b c)`) | **é a própria conjectura** | K9/K10 provam `CommonPrime ↔ CommonDivisor`, e `bealConjecture_iff_commonDivisorProducer` mostra que o produtor é equivalente a Beal — é reformulação, não redução | Prova da conjectura (casos conhecidos: expoentes iguais = Fermat–Wiles; para cada terna fixa com `1/x+1/y+1/z < 1` há só finitas soluções primitivas — Darmon–Granville — o que não dá o caso geral) |
| B2 | `certifyBeal (h : BealConjecture)` (K7) | **condicional por construção** | Recebe a conjectura como hipótese | Nenhuma correção; não contar como fechamento |
| B3 | Ponte para o alvo do portão | **feita** | `bealConjecture_iff_exact` e `beal_of_producer` certificados (seção 0) | — |
| B4 | Compilação | — | `MCore.lean` importa módulos (`AttackDAG`, `Audit`, `Frontier`, …) ausentes aqui | CI que compila a partir do commit de origem (`provenance/`) |

## 4. Falsificador exato

Um certificado finito: `a^x + b^y = c^z` com `x, y, z > 2` e `gcd(a, b, c) = 1` — verificável por
computação direta (M-Core: `ATK.Closure.beal_false_iff`, `ATK.Closure.beal_refuted_by_witness`;
aqui: `counterexample_refutes`, `noCommonPrime_refutes_beal`). O caso de fronteira
`1/x+1/y+1/z ≥ 1` mostra que a hipótese `> 2` é necessária (M-Core:
`ATK.Closure.fermat_catalan_boundary`).

## 5. Condição para mudar o estado

CONDICIONAL → FECHADO somente com uma declaração de tipo `ATK.Exact.Beal` (ou a negação) aceita pelo
portão, sem `sorry`, só com os axiomas padrão e sem a conclusão entre as hipóteses.

---

**English summary.** Status CONDITIONAL (kernel-checked bridge `GCDLowerBoundProducer → ATK.Exact.Beal`, 7/7 certified). The local `BealConjecture` is a faithful
statement of Beal. The "producer" `GCDLowerBoundProducer` is proven equivalent to it (a
reformulation, not a reduction); `certifyBeal` takes the conjecture as a hypothesis. The bridge to the
gate target is now certified; what remains is a proof of H. Falsifier: an explicit
coprime solution with exponents > 2.
