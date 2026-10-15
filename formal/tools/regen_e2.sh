#!/bin/bash
# Regenerate `Gen/E2` -- the ECDSA2 meaning bridge -- end to end, in the order that built.
#
# Usage: regen_e2.sh [SCRATCH] [SIDECAR]
#   SCRATCH  per-lemma files and cone dumps (default /tmp/e2scratch); safe to reuse, each stage
#            skips work already present
#   SIDECAR  from `tools/regen_artifact.sh ecdsa2` (default /tmp/regen-Ecdsa2/ecdsa2.sidecar)
#
# Recorded 2026-10-15, after this sequence produced all 146 modules (`Gen/E2`, `Bridge/Ecdsa2`,
# `Gen/Ecdsa2/Ecdsa2Meaning`) with no `sorry`, no `axiom` and no `native_decide`.  Before that,
# no part of it had been run end to end since the machine it was written on, and every stage
# failed only once the stage before it succeeded.  The order below is load-bearing:
#
#   * the mux stage reads each round's triple back out of the *merged* loop modules, so the
#     loops are merged before muxes are generated;
#   * the bit stage reads the 256 wires back out of the bit-sum modules, so those come first;
#   * `gen_loop_ok` needs `looptab.json`/`chain.json`, which need the per-round loop lemmas.
#
# Each read-back exists so two lemma families cannot disagree about which node a value is.
set -eu
F=$(cd "$(dirname "$0")/.." && pwd)
R=$(cd "$F/../rust" && pwd)
S=${1:-/tmp/e2scratch}
SC=${2:-/tmp/regen-Ecdsa2/ecdsa2.sidecar}
GEN="$F/circuits/quadcert/Gen/E2"
T="$F/tools"
mkdir -p "$S" "$GEN"

say() { printf '\n== regen_e2: %s\n' "$*"; }

[ -s "$SC" ] || { echo "regen_e2: no sidecar at $SC -- run tools/regen_artifact.sh ecdsa2" >&2; exit 1; }
[ -s "$F/circuits/quadcert/Gen/Ecdsa2/Ecdsa2Meaning.lean" ] || {
  echo "regen_e2: Gen/Ecdsa2/Ecdsa2Meaning.lean is missing -- rerun tools/regen_artifact.sh ecdsa2," >&2
  echo "          which now emits it; E2Digits and E2Small import it" >&2; exit 1; }

# Write to a temporary and move only on success, so a failing stage cannot empty the tree.
emit() { local out=$1; shift; if "$@" > "$out.new"; then mv "$out.new" "$out"; else rm -f "$out.new"; return 1; fi; }

say "layout"
python3 "$T/gen_layout.py" "$GEN"

say "loops: one cone dump, 768 lemmas, mux reconciliation"
"$T/gen_all_loops.sh" "$S" "$SC"
"$T/merge_all.sh" "$S"

say "muxes (read the triples back out of the merged loops)"
"$T/gen_all_muxes.sh" "$S" "$SC"

say "bit sums, then bits (read the wires back out of the bit sums)"
"$T/gen_all_bitsums.sh" "$S" "$SC"
"$T/gen_all_bits.sh" "$S" "$SC"
"$T/merge_all.sh" "$S"

say "comparator and slice cones, one pass"
if [ ! -s "$S/ltcones/index.json" ]; then
  mkdir -p "$S/ltcones"
  DUMP_CONES="$S/ltcones" DUMP_CONES_PATHS=rx_lt_order,nms_lt_order,slice_x,slice_y \
    cargo run -q --release --manifest-path "$R/Cargo.toml" \
    --example meaning_gen -p compile-compiler -- "$SC" /dev/null
fi
first() { ls "$1"*.json 2>/dev/null | head -1; }

say "comparator, 256 leaves"
emit "$GEN/E2LtRx.lean"  python3 "$T/gen_lt_meaning.py" \
  "$(first "$S/ltcones/rx_lt_order")"  "$(first "$S/bitcones/rx_eq")"  lt_rx_order
emit "$GEN/E2LtNms.lean" python3 "$T/gen_lt_meaning.py" \
  "$(first "$S/ltcones/nms_lt_order")" "$(first "$S/bitcones/nmsinv")" lt_nms_order

say "slices"
mkdir -p "$S/slices"
for K in 0 1 2 3; do for C in X Y; do
  c=$(echo "$C" | tr XY xy)
  emit "$S/slices/slice${C}_${K}.lean" python3 "$T/gen_addE_meaning.py" \
    "$S/ltcones/slice_${c}_${K}.json" "slice${C}_${K}" "$C"
done; done
emit "$GEN/E2SliceX.lean" python3 "$T/merge_slices.py" E2SliceX \
  "$S"/slices/sliceX_{0,1,2,3}.lean "$S"/slices/sliceY_{0,1,2,3}.lean

say "loop assembly"
python3 "$T/gen_looptab.py" "$S"
emit "$GEN/E2LoopOk.lean" python3 "$T/gen_loop_ok.py" "$S" loop_ok

say "composition"
python3 "$T/gen_rest.py"   "$GEN"
python3 "$T/gen_cmp_ok.py" "$GEN"
python3 "$T/gen_final.py"  "$GEN"

say "closure"
python3 - "$F/circuits/quadcert" <<'PY'
import re, glob, os, sys
os.chdir(sys.argv[1])
have = {os.path.basename(p)[:-5] for p in glob.glob("Gen/E2/*.lean")}
need = {m.group(1) for p in glob.glob("Gen/E2/*.lean") + glob.glob("Bridge/Ecdsa2/*.lean")
        for m in re.finditer(r'^import quadcert\.Gen\.E2\.(\w+)', open(p).read(), re.M)}
miss = sorted(need - have)
print(f"Gen/E2: {len(have)} modules, {len(need)} imported, {len(miss)} missing {miss if miss else ''}")
sys.exit(1 if miss else 0)
PY
echo "regen_e2: next -> tools/leanseq quadcert 36 '^(Gen\\.Ecdsa2\\.Ecdsa2Meaning|Bridge\\.Ecdsa2\\.|Gen\\.E2\\.)'"
