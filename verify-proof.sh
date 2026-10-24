#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Requires the pinned Lean toolchain plus matching leanexport, leanchecker,
# nanoda_bin, and Python3 on PATH. No downloads or installations are performed.
mkdir -p .verification
primitive=(Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam)
modules=(FinalEquivalence)
if (($#)); then modules=("$@"); fi
for module in "${modules[@]}"; do
  case "$module" in
    FinalEquivalence) targets=(K230Verification.exact_11487_equivalence K230Verification.exact_plane_iff_neverHalts K230Verification.neverHalts_implies_exact_plane K230Verification.exact_plane_implies_neverHalts K230Verification.full_plane_objective);;
    MachineRun) targets=(K230Verification.spaceTime_iff_neverHalts);;
    ExactSet) targets=(K230Verification.fullPlaneSet_card);;
    Recognizability) targets=(Wang156.D1_six Wang156.D2_horizontal_eight Wang156.D2_vertical_eight);;
    GlobalRecognition) targets=(Wang156.exact_desubstitution Wang156.exact_arbitrary_supertile);;
    FullPlaneProjection) targets=(K230Verification.exact_base_valid K230Verification.exact_full_tiling_supertile_lift);;
    TMCoreBridge) targets=(K230Verification.tmComp_iff_allowed);;
    ExactForward) targets=(K230Verification.exact_plane_implies_neverHalts);;
    ExactTarget) targets=(K230Verification.exact_plane_iff_windows);;
    *) printf 'Unknown checked module: %s\n' "$module" >&2; exit 2;;
  esac
  lake build "+$module"
  lake env leanexport "$module" -- "${primitive[@]}" "${targets[@]}" > ".verification/$module.ndjson"
  leanchecker --silent --from-export ".verification/$module.ndjson" > ".verification/$module.leanchecker.log" 2>&1
  python3 - "$module" <<'PY'
import json,sys
from pathlib import Path
m=sys.argv[1]
Path(f'.verification/{m}.nanoda.json').write_text(json.dumps({
 'use_stdin':False,'export_file_path':f'.verification/{m}.ndjson',
 'permitted_axioms':['propext','Quot.sound','Classical.choice'],
 'unpermitted_axiom_hard_error':True,'num_threads':2,
 'nat_extension':True,'string_extension':True}))
PY
  nanoda_bin ".verification/$module.nanoda.json" > ".verification/$module.nanoda.log" 2>&1
  printf '%s: Lean kernel and strict NanoDa replay passed.\n' "$module"
done
