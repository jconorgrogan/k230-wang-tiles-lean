#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Serial topological order bounds peak memory for exact finite certificates.
for m in RowSimulation FiniteWindow MachineRun WangCompactness BoardChannels FreeOffsets PhaseHierarchy NestedBoards ExactTable PatchSemantics ArcDomains ArcCertificates Adjacency Recognizability BaseFacts GlobalRecognition MachineData FullPlaneData FullPlaneCount SortProof Distinctness ExactSet ExactTarget FullPlaneProjection ConcreteRoles TMCoreBridge; do
  lake build "+$m"
done
lake build
