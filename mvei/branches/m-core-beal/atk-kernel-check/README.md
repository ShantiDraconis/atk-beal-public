# m-core-beal — branch `atk-kernel-check`

Lean sources from the branch `atk-kernel-check` of the private repository `ShantiDraconis/m-core-beal`, commit `36f4c915552bdd7057cacfc025eab2f531a52e69` (2026-10-12T21:14:50+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 4, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 5 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `529f1cfbecb13b19443123a0dce6664d72acc48b42266da894f76bd9114d71ed`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/atk-kernel-check/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.BealDescent.beal_of_descent` | `atk-kernel/ATK/BealDescent.lean`:55 | fechado |
| `ATK.BealDescent.descent_iff_beal` | `atk-kernel/ATK/BealDescent.lean`:71 | fechado |
| `ATK.BealDescent.descent_of_beal` | `atk-kernel/ATK/BealDescent.lean`:63 | fechado |
| `ATK.BealDescent.no_primitive_of_descent` | `atk-kernel/ATK/BealDescent.lean`:43 | fechado |
