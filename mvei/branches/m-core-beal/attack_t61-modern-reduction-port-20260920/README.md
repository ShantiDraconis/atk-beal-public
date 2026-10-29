# m-core-beal — branch `attack/t61-modern-reduction-port-20260920`

Lean sources from the branch `attack/t61-modern-reduction-port-20260920` of the private repository `ShantiDraconis/m-core-beal`, commit `3393c2c1e1da5ee88481cbe116f40e6fcde5daf4` (2026-09-20T22:13:49+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 15 — closed 4, conditional 0, open 0, proof error 2, not reached 9, no result 0.
* History: 110 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `4c88b67a7cc8ae66fe0eaca773a44c3b1ac85389baeb42d818f1393da299bf5f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/attack_t61-modern-reduction-port-20260920/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.T61_c4_matches_T32_kernel` | `lean/MCore/T61.lean`:81 | erro |
| `MCore.T61_delta_matches_T24_kernel` | `lean/MCore/T61.lean`:93 | erro |
| `MCore.T61_freyCurveQ_c4` | `lean/MCore/T61.lean`:67 | fechado |
| `MCore.T61_freyCurveQ_delta` | `lean/MCore/T61.lean`:74 | fechado |
| `MCore.T61_freyCurveZ_c4` | `lean/MCore/T61.lean`:32 | fechado |
| `MCore.T61_freyCurveZ_delta` | `lean/MCore/T61.lean`:49 | fechado |
| `MCore.T62_freyCurveQ_isIntegral` | `lean/MCore/T62.lean`:146 | nao_alcancado |
| `MCore.T62_isMinimal_of_valuation_c4_eq_one` | `lean/MCore/T62.lean`:100 | nao_alcancado |
| `MCore.T62_natPrime_to_corePrime` | `lean/MCore/T62.lean`:22 | nao_alcancado |
| `MCore.T62_primePlace_natGenerator` | `lean/MCore/T62.lean`:40 | nao_alcancado |
| `MCore.T63_freyCurveQ_c4_eq_natKernel` | `lean/MCore/T63.lean`:53 | nao_alcancado |
| `MCore.T63_freyCurveQ_delta_eq_natKernel` | `lean/MCore/T63.lean`:60 | nao_alcancado |
| `MCore.T63_freyCurve_hasMultiplicativeReduction_at_odd_bad_prime` | `lean/MCore/T63.lean`:67 | nao_alcancado |
| `MCore.T63_isUnit_natCast_localRing` | `lean/MCore/T63.lean`:38 | nao_alcancado |
| `MCore.T63_natCast_mem_primePlace_iff` | `lean/MCore/T63.lean`:20 | nao_alcancado |
