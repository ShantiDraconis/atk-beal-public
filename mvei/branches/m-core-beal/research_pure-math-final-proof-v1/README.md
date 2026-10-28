# m-core-beal — branch `research/pure-math-final-proof-v1`

Lean sources from the branch `research/pure-math-final-proof-v1` of the private repository `ShantiDraconis/m-core-beal`, commit `a592aba90040cb8dd3e1061bb0ae619218dfd9ad` (2026-09-20T14:14:16+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 34 — closed 18, conditional 0, open 0, proof error 1, not reached 15, no result 0.
* History: 60 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `37835522b723ed7ac30fab0e277ca6a8f7a19cb31ed32f6f9ca071dbeb8b2471`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/research_pure-math-final-proof-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Audit8x5.A_axis_is_matched` | `lean/MCore/Audit8x5.lean`:87 | fechado |
| `MCore.Audit8x5.HC_axis_is_blocking` | `lean/MCore/Audit8x5.lean`:88 | fechado |
| `MCore.Audit8x5.K_axis_is_matched` | `lean/MCore/Audit8x5.lean`:83 | fechado |
| `MCore.Audit8x5.Q_axis_is_matched` | `lean/MCore/Audit8x5.lean`:85 | fechado |
| `MCore.Audit8x5.S_axis_is_matched` | `lean/MCore/Audit8x5.lean`:86 | fechado |
| `MCore.Audit8x5.beal_iff_deltaStar` | `lean/MCore/Audit8x5.lean`:23 | fechado |
| `MCore.Audit8x5.constant_match` | `lean/MCore/Audit8x5.lean`:49 | fechado |
| `MCore.Audit8x5.no_placebo_endpoint` | `lean/MCore/Audit8x5.lean`:56 | fechado |
| `MCore.Audit8x5.not_all_five_match` | `lean/MCore/Audit8x5.lean`:89 | fechado |
| `MCore.Audit8x5.quantifier_match_iff_deltaStar` | `lean/MCore/Audit8x5.lean`:33 | fechado |
| `MCore.Audit8x5.scaling_match` | `lean/MCore/Audit8x5.lean`:41 | fechado |
| `MCore.Research.return_to_primary` | `lean/MCore/Research/ParallelClosure.lean`:10 | fechado |
| `MCore.V5.S_maps_bottom_to_point` | `lean/MCore/V5/Surgery.lean`:11 | nao_alcancado |
| `MCore.V5.S_preserves_payload` | `lean/MCore/V5/Surgery.lean`:14 | nao_alcancado |
| `MCore.V5.beal_of_arithmeticResidue` | `lean/MCore/V5/BealReduction.lean`:48 | nao_alcancado |
| `MCore.V5.bot_absorbs_add` | `lean/MCore/V5/Algebra.lean`:30 | nao_alcancado |
| `MCore.V5.counterexample_payload_preserved` | `lean/MCore/V5/BealPayload.lean`:17 | nao_alcancado |
| `MCore.V5.endpoint_hypothesis_blocks` | `lean/MCore/V5/Firewall.lean`:16 | fechado |
| `MCore.V5.finalProofRequires_is_residue` | `lean/MCore/V5/ArithmeticFrontier.lean`:14 | nao_alcancado |
| `MCore.V5.model_distinguishes` | `lean/MCore/V5/Algebra.lean`:40 | nao_alcancado |
| `MCore.V5.omegaBottom_payload` | `lean/MCore/V5/OmegaBottom.lean`:14 | fechado |
| `MCore.V5.omegaPoint_payload` | `lean/MCore/V5/OmegaPoint.lean`:14 | fechado |
| `MCore.V5.omega_ne_bot` | `lean/MCore/V5/Algebra.lean`:33 | nao_alcancado |
| `MCore.V5.omega_preserves_counterexample_payload` | `lean/MCore/V5/BealReduction.lean`:16 | nao_alcancado |
| `MCore.V5.prime_dvd_cpow_of_dvd_a_b` | `lean/MCore/V5/BealReduction.lean`:19 | nao_alcancado |
| `MCore.V5.zero_mul_omega_eq_bot` | `lean/MCore/V5/Algebra.lean`:27 | nao_alcancado |
| `MCore.commonDivisorResidual_holds` | `lean/MCore/V24CommonDivisorResidual.lean`:21 | nao_alcancado |
| `MCore.noCommonPrimeCandidate_iff_not_beal` | `lean/MCore/BealSpecification.lean`:47 | fechado |
| `MCore.noCommonPrimeCandidate_iff_primitive` | `lean/MCore/BealResidualSystem.lean`:9 | fechado |
| `MCore.no_independent_truth_state_v24` | `lean/MCore/V24MiddleIndependence.lean`:38 | nao_alcancado |
| `MCore.normalized_has_no_common_divisor` | `lean/MCore/V24CommonDivisorResidual.lean`:12 | nao_alcancado |
| `MCore.primitiveObstruction_iff_beal` | `lean/MCore/BealResidualSystem.lean`:40 | erro |
| `MCore.primitive_has_no_common_divisor` | `lean/MCore/V24CommonDivisorResidual.lean`:4 | nao_alcancado |
| `MCore.primitive_iff_normalized` | `lean/MCore/BealResidualSystem.lean`:28 | fechado |
