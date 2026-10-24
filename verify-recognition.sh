#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
for m in ExactTable PatchSemantics ArcDomains ArcCertificates Adjacency Recognizability; do
  lean -o "$m.olean" "$m.lean" > "$m.build.log" 2>&1
done
leanexport Recognizability -- Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam Wang156.D1_six Wang156.D2_horizontal_eight Wang156.D2_vertical_eight > Recognizability.ndjson
leanchecker --silent --from-export Recognizability.ndjson > Recognizability.leanchecker.log 2>&1
nanoda_bin Recognizability.nanoda.json > Recognizability.nanoda.log 2>&1
printf '%s\n' 'All local recognizability checks passed.'
