# What the external ZFC interpretation uses

## The Lean theorem

The submission's precise mathematical endpoint is the literal 11,487-tile set's unseeded whole-plane tilability if and only if the literal K230 machine never halts from its ordinary blank initial configuration. The same statement asserts that the list contains exactly 11,487 tiles and no duplicates.

This statement does not define ZFC proofs or consistency, and does not assert a formal ZFC-independence theorem. Its Solution has no assumption saying that ZFC is consistent or that the machine never halts.

## The separately published Rocq theorem

At [commit a8312f0ca703bc81baac16695a437a7d3788f690](https://github.com/elliotglazer/k230-rocq/commit/a8312f0ca703bc81baac16695a437a7d3788f690), Glazer's axiom-free development supplies the endpoints [tm230_halts_iff_ZFC_inconsistent and tm230_nonhalting_iff_ZFC_consistent](https://github.com/elliotglazer/k230-rocq/blob/a8312f0ca703bc81baac16695a437a7d3788f690/coq/tm/Correct230.v#L9-L19).

The formal consistency notion is absence of a finite classical first-order natural-deduction proof of falsity from StandardZFC. [StandardZFC](https://github.com/elliotglazer/k230-rocq/blob/a8312f0ca703bc81baac16695a437a7d3788f690/coq/settheory/KQuotZFC.v#L12-L13) includes Foundation and Choice in addition to the underlying ZF axioms and schemes. These equivalences do not assume or prove that ZFC is consistent.

An independent finite-data audit found agreement of all 460 Lean transition codes with both the pinned machine serialization and the pinned Rocq transition table. Serializing the recovered machine gives SHA-256:

`e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`

The [upstream axiom-free workflow](https://github.com/elliotglazer/k230-rocq/actions/runs/39466235683) reports a successful rebuild and `coqchk` for that commit. This is upstream evidence, not an independent Rocq replay performed by this project.

The Lean machine uses an absolute integer-indexed tape and head position. The Rocq machine uses two infinite streams centered at the head. Equality of transition tables alone does not certify their semantic correspondence or translate the Rocq proof into Lean. Any separately checked representation correspondence is distinguished from verification of the complete Rocq consistency development.

## What may and may not be concluded

Combining the Lean tiling theorem with the externally established mathematical K230 consistency equivalence gives the intended consistency interpretation. The external result and its cross-prover identification are not part of this submission's Lean kernel-checked dependency chain. No custom Lean axiom is introduced to conceal that boundary.

An assertion about what ZFC itself can prove requires a further internal formalizability and incompleteness argument. Mere consistency supports the usual Gödel-II unprovability direction when the equivalence is available internally; excluding a proof of the negation requires an appropriate stronger soundness condition. This submission does not claim that those metamathematical obligations were formalized in Lean.

## Provenance and licensing

No `k230.tm` or custom Rocq source file is included in this repository. The transition facts were recovered independently from the supplied tile data and checked against the pinned external source. The [upstream licensing notice](https://github.com/elliotglazer/k230-rocq/blob/a8312f0ca703bc81baac16695a437a7d3788f690/THIRD_PARTY.md#L39-L44) distinguishes named third-party notices from a blanket licence for custom sources. The Apache-2.0 licence here covers the newly written proof/code, not the external Rocq development or the original construction archive.
