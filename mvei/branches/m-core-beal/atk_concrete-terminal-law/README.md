# m-core-beal — branch `atk/concrete-terminal-law`

Lean sources from the branch `atk/concrete-terminal-law` of the private repository `ShantiDraconis/m-core-beal`, commit `baec1da93c59fab31b34643c20b5831d02e84e88` (2026-10-04T17:51:02+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 4, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 4 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `a0aad188dbfff150cc93ca52a865f32726286e7898dff8d54eb53b9bd0e8b2b8`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/atk_concrete-terminal-law/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.beal_terminal_cert_refute_disjoint` | `lean/MCore/BealTerminalLaw.lean`:58 | fechado |
| `MCore.beal_terminal_certifies_iff_gcdLowerBound` | `lean/MCore/BealTerminalLaw.lean`:24 | fechado |
| `MCore.beal_terminal_refutes_iff_counterexample` | `lean/MCore/BealTerminalLaw.lean`:28 | fechado |
| `MCore.not_beal_terminal_certifies_iff_refutes` | `lean/MCore/BealTerminalLaw.lean`:44 | fechado |
