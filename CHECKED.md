# What has actually been checked

This is a work-in-progress proof repository, not a completed Palomar submission.

- `K230Verification.fullPlaneSet_card` in `ExactSet.lean` establishes that the generated finite set has exactly 11,487 distinct tiles. The cardinality proof combines individual template certificates and distinct base/channel groups, rather than counting duplicate list entries.
- `Wang156.D1_six` and both D2 theorems prove exact local recognition for the literal 156-tile base table. Short, deterministic domain-pruning certificates exclude all 29 exceptional aligned blocks.
- `Wang156.recognition` and `exact_arbitrary_supertile` remove the abstract recognition hypothesis: every valid base-plane tiling has the phase-aware hierarchy at every order.
- `tmComp_iff_allowed` binds the actual computation-tile family to the specified K230 transition function, including exactly the entered-state merge tiles.
- `spaceTime_iff_neverHalts` proves the generic unbounded row compiler equivalent to ordinary machine nonhalting. This does not itself prove that the full-plane construction forces those rows.
- `exact_plane_iff_windows` gives the compactness step for the exact full-plane tile alphabet. Its finite-window side quantifies over every size, not finitely many tested examples.

Lean kernel replay and strict independent NanoDa replay results, exact source hashes, and dependency pins are recorded in `verification.json`. Only the standard logical axioms `propext`, `Quot.sound`, and `Classical.choice` are permitted. No `sorry`, custom mathematical axiom, `native_decide`, or `Lean.ofReduceBool` is used to close these claims.

Still open: extracting correctly initialized machine boards from the concrete hierarchy, constructing compatible decorated finite boards at every scale, joining these to the full-plane equivalence, and establishing the consistency interpretation without importing the external Rocq result as an axiom. Neither a component theorem nor successful finite data checks close those obligations.

## Reproduction

Use the pinned Lean toolchain and run `bash build-serial.sh` (or `lake build` when sufficient memory is available). The local-recognition replay can additionally be run with `bash verify-recognition.sh` when the matching `leanexport`, `leanchecker`, and `nanoda_bin` executables are available on PATH. It performs its own builds and selected-theorem export. These are local checks, not the Palomar registry's official intake or validation process.

The original construction and immutable TSV remain in the separate construction repository. `recognition-data-provenance.json` records finite source-to-table audit details; those audits are distinguished from the universally quantified Lean theorems.
