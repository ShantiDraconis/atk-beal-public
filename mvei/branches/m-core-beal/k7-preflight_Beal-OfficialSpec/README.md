# m-core-beal — branch `k7-preflight/Beal-OfficialSpec`

Lean sources from the branch `k7-preflight/Beal-OfficialSpec` of the private repository `ShantiDraconis/m-core-beal`, commit `664d8b6092c88572c6ab5d11d23f6460f51cedcc` (2026-09-15T20:10:41+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 3 — closed 3, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 1 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `f772886deeac014111b62d7ba8f91664751b49880649ab49c57d9e2c6ba15d25`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-beal/k7-preflight_Beal-OfficialSpec/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.k7_spec_not_certified` | `lean/MCore/K7.lean`:11 | fechado |
| `MCore.k7_spec_not_proved` | `lean/MCore/K7.lean`:10 | fechado |
| `MCore.k7_spec_status_openBridge` | `lean/MCore/K7.lean`:9 | fechado |
