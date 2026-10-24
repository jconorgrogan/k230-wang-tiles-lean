# K230: 11,487 unseeded Wang tiles and machine nonhalting

This Lean development proves the exact full-plane computation equivalence:

> The specified 11,487 distinct Wang tiles tile the whole integer plane if and only if the specified K230 Turing machine never halts from its blank initial configuration.

There is no seed tile, boundary condition, distinguished origin, or prescribed tile at any coordinate. Tiles may be translated, not rotated or reflected.

## Exact statement

The theorem `K230Verification.exact_11487_equivalence` in [FinalEquivalence.lean](FinalEquivalence.lean) proves:

```lean
exactFullPlaneTiles.length = 11487 ∧ exactFullPlaneTiles.Nodup ∧
  (ExactPlane ↔ K230NeverHalts)
```

`ExactPlane` assigns a tile to every pair of integers and requires matching edges at every horizontal and vertical adjacency. `K230NeverHalts` quantifies over every finite iterate of the exact deterministic transition table, starting in state 0 at head position 0 on the entirely blank two-way tape. The alphabet and machine data are explicit.

[Challenge.lean](Challenge.lean) is the standalone statement, including the literal data. Its sole `sorry` is the deliberately unproved challenge declaration required for statement comparison. [Solution.lean](Solution.lean) imports the completed proof, not the challenge. No proof depends on that placeholder.

## How the proof works

1. Every valid plane tiling projects to the exact 156-tile base system. Finite certificates establish the recognition rules, from which arbitrary-scale computing boards follow.
2. Their channels force a unique blank initial head and correctly routed finite K230 computations. Boards of all scales imply survival for every finite time.
3. Conversely, a nonhalting computation supplies finite decorated boards at every scale. Smaller boards are recursively inserted with matching full edge colors. Compactness then gives a tiling of the entire plane.

This is a universal proof, not an extrapolation from finite simulations. The concrete compiler equivalence is instantiated for K230; no theorem about every partial Turing machine is claimed.

## Verification and submission status

[CHECKED.md](CHECKED.md) and [verification.json](verification.json) state the exact completed checks and remaining registry gates. The pinned reusable Palomar workflow is a predictive mechanical preflight, not a submission or registration. No Palomar acceptance is claimed.

The only permitted logical axioms are `propext`, `Quot.sound`, and `Classical.choice`. The proof contains no `sorry`, custom mathematical axiom, `native_decide`, or `Lean.ofReduceBool`.

## Reproduce

Use the pinned Lean toolchain and Mathlib revision in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
bash build-serial.sh
bash verify-proof.sh FinalEquivalence
lake comparator --config comparator.json
```

Serial building bounds peak memory for exact finite certificates. The proof replay script also requires the matching `leanexport`, `leanchecker`, and `nanoda_bin` executables on PATH. Comparator additionally requires its supported bubblewrap sandbox. Neither script disables sandbox restrictions.

## What this says about ZFC

Glazer's separately formalized Rocq result connects K230 nonhalting with ZFC consistency. That result is external context, not an axiom or theorem proved inside this Lean project. The selected submission statement is the precise tiling-to-machine equivalence, not a complete Lean formalization of ZFC consistency or independence. See [EXTERNAL_CONSISTENCY.md](EXTERNAL_CONSISTENCY.md).

The exact tile alphabet was compared as a set against the user-supplied full-plane construction TSV. Enumeration order differs. All 460 machine transition codes were compared with the pinned official K230 serialization. These finite source-data comparisons establish provenance, not the infinite tiling theorem.

## Authorship, sources and licence

Responsible human maintainer: **jconorgrogan**. AI systems produced the substantive new proof and code under the maintainer's direction, including separate semantic and source-data audits. No independent human peer review or novelty claim is made. [formalization.yaml](formalization.yaml) records the scope and disclosures.

Apache-2.0 applies only to the new proof/code in this repository. The separately supplied construction archive remains unchanged and unlicensed. No `k230.tm` or custom source files from `elliotglazer/k230-rocq` are included or relicensed.
