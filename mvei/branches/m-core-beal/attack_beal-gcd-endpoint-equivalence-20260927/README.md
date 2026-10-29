# m-core-beal — branch `attack/beal-gcd-endpoint-equivalence-20260927`

Lean sources from the branch `attack/beal-gcd-endpoint-equivalence-20260927` of the private repository `ShantiDraconis/m-core-beal`, commit `c77d441fc4bb0837a4afdeef18d3ccb9b1d64905` (2026-09-27T18:56:21+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 8 — closed 6, conditional 0, open 1, proof error 1, not reached 0, no result 0.
* History: 150 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `8b3e035c75e09049d35e031b37ca240eeae6244b465d3f76262fa6a8d5ff04f6`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/attack_beal-gcd-endpoint-equivalence-20260927/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BealAcceptedClosurePipelineState_is_unresolved` | `lean/MCore/BealAcceptedClosurePipeline.lean`:54 | fechado |
| `MCore.acceptedClosureObject_closes_beal` | `lean/MCore/BealAcceptedClosurePipeline.lean`:12 | fechado |
| `MCore.commonDivisorEndpoint_closes_beal` | `lean/MCore/BealCommonDivisorEndpoint.lean`:45 | fechado |
| `MCore.finalRoot_closes_beal` | `lean/MCore/BealAcceptedClosurePipeline.lean`:41 | fechado |
| `MCore.finalRoot_refutation_exclusive` | `lean/MCore/BealAcceptedClosurePipeline.lean`:44 | fechado |
| `MCore.gcdEndpoint_closes_beal` | `lean/MCore/BealGcdEndpoint.lean`:21 | aberto-sorry |
| `MCore.gcdEndpoint_to_commonDivisorEndpoint` | `lean/MCore/BealGcdEndpoint.lean`:12 | erro |
| `MCore.universalCommonDivisor_to_commonPrime` | `lean/MCore/BealCommonDivisorEndpoint.lean`:12 | fechado |
