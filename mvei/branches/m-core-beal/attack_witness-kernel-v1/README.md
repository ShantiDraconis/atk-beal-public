# m-core-beal — branch `attack/witness-kernel-v1`

Lean sources from the branch `attack/witness-kernel-v1` of the private repository `ShantiDraconis/m-core-beal`, commit `a8da5b8c89d00c6b2369c867d748d0d3855dc509` (2026-09-19T11:24:49+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 5 — closed 5, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 3 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `00105c54ff2d2c42bf7600d2d10a536aa7a9a732320ae73108e61d3b24fc7078`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/attack_witness-kernel-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.beal_constructor_closes` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:24 | fechado |
| `MCore.BackwardAudit.beal_constructor_iff_contract` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:20 | fechado |
| `MCore.BackwardAudit.beal_witness_constructor_still_open` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:31 | fechado |
| `MCore.BackwardAudit.common_prime_contract_to_constructor` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:15 | fechado |
| `MCore.BackwardAudit.constructor_to_common_prime_contract` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:10 | fechado |
