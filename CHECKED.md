# Verification record and boundaries

## Mathematical endpoint

`K230Verification.exact_11487_equivalence` proves that the explicit list contains exactly 11,487 distinct tiles and that it tiles the entire integer plane if and only if the exact K230 machine never halts from its blank initial configuration.

There are no geometric, routing, initialization, seed, boundary, nonhalting, or consistency hypotheses left on this equivalence. Nonhalting is one side of the equivalence, not an assumed theorem.

## Proof checks

The frozen endpoint graph contains 124 custom Lean modules. Each was rebuilt from source in topological order in a separate clean directory, and the final theorem dependency export completed. Every one of the 124 clean builds, the final proof export, independent Lean kernel replay, and strict NanoDa replay exited 0. All 124 frozen source hashes were unchanged after checking. `verification.json` records the full source graph, timings, exit codes and exact export hash.

The forward extraction and reverse exposed-board constructor have separately passed elaboration, export, Lean kernel replay and strict NanoDa replay. The final clean combined graph is checked independently again, not inferred to pass merely because its components passed.

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. The proof does not use `sorry`, custom axioms, `native_decide`, `Lean.ofReduceBool`, or skipped kernel checking. The one deliberate placeholder in `Challenge.lean` is on the standalone statement-only target. `Solution.lean` does not import Challenge, and that placeholder is not a premise of the proof.

## Statement and source audit

A separate semantic audit checked:

- unrestricted assignments on all of Z × Z, both adjacency constraints, and fixed tile orientation;
- state 0, head position 0, an entirely blank two-way tape, exact transition decoding and every finite computation time;
- all-scale board quantifiers, initialized computation, strictly smaller recursive children, full-color seams and finite-window neighbor margins;
- noncircular dependencies between forward extraction, reverse construction and the final equivalence;
- the standalone Challenge's explicit data and definitions matching the Solution endpoint.

The Lean tile alphabet matches the immutable construction TSV as a set, not in enumeration order. `source_data_audit.json` identifies both hashes and records the finite set comparison. `official_machine_audit.json` records agreement of all 460 transition codes with the pinned official K230 serialization. These finite comparisons are provenance checks, not substitutes for the universal proof.

## Comparator and registry

A local Comparator invocation was blocked before checking by the required bubblewrap sandbox: `bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted`. This is not a Comparator pass or a mathematical rejection. The sandbox was not disabled.

The pinned GitHub Actions reusable workflow runs the official predictive mechanical preflight with a fresh build and protected standalone Challenge. Its result must be checked separately. A preflight is not registry submission, editorial review, acceptance or registration. No such acceptance is claimed here.

## External consistency interpretation

The selected Lean endpoint is tile-to-machine equivalence. It does not formalize ZFC syntax, consistency or incompleteness. Glazer's separate Rocq result is external mathematical context; no custom Lean axiom imports that result. See `EXTERNAL_CONSISTENCY.md` for the precise provenance and cross-prover boundary.

## Reproduction

Run `bash build-serial.sh` with the pinned Lean/Mathlib environment, then `bash verify-proof.sh FinalEquivalence` with the matching exporter, Lean checker and NanoDa executable on PATH. For the standalone statement comparison, use `lake comparator --config comparator.json` in an environment supporting its mandatory sandbox. Verification scripts do not download software or disable the sandbox.
