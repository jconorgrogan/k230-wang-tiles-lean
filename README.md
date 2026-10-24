# K230 Wang tiles: Lean verification

A Wang tile is a square with a colour on each edge. Copies cover the integer grid without rotation, and touching edges must have the same colour. This project is working toward a proof that the supplied set of 11,487 tiles covers the entire plane exactly when K230 never halts, with no seed or boundary condition.

**Work in progress. The full-plane equivalence is not yet formally proved, submitted to Palomar, or registered.**

The original construction and tile list remain in [k230-wang-tiles](https://github.com/jconorgrogan/k230-wang-tiles). This separate repository holds newly written Lean verification work. It does not relicense the supplied archive or include files from Glazer's Rocq development.

The proof has three main parts: the base tiles must force computation boards at every scale; each board must run the correct initialised machine computation; and a nonhalting run must yield a genuine whole-plane tiling. Finite example patches alone do not establish any infinite-plane claim.

The verification work includes universal row-simulation and finite-head-displacement proofs, finite-alphabet Wang compactness, exact machine-data checks, and local recognizability certificates under development. Each checked component will be identified separately from the still-open assembly.

Glazer's [Rocq development](https://github.com/elliotglazer/k230-rocq) proves the separate equivalence between K230 nonhalting and ZFC consistency. That external theorem is not being introduced as a Lean axiom. A fully Lean-checked consistency interpretation remains a separate obligation.

New proof and code in this repository are released under Apache-2.0. Mathematical sources and external dependencies retain their own licensing and attribution. The work uses substantial AI assistance; its responsible human maintainer is jconorgrogan.
