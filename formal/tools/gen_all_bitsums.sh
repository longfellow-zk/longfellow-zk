#!/bin/bash
# Emit the three bit-sum modules: `E2BitSumE`, `E2BitSumRx`, `E2BitSumNms`.
#
# Each proves that one witness is `bitsLE [w0 … w255]` over the circuit's own wires, with the
# 256 `wk` left opaque.  That cut is the point: each bit is a degree-7 table interpolant in its
# digit, so expanding them makes a 2,313-node cone hopeless, while holding them opaque leaves a
# linear statement.  `gen_all_bits.sh` then proves each `wk` *is* the digit's bit, and reads the
# wire list back out of these modules so the two families cannot disagree about which node a
# bit is.
#
# There was no driver for this stage; the three invocations differ only in cone, theorem name
# and kind, and `nmsinv` is `inv` (the sum is invertible) rather than `eq` (a witness equals it).
set -u
F=$(cd "$(dirname "$0")/.." && pwd)
R=$(cd "$F/../rust" && pwd)
S=${1:?usage: gen_all_bitsums.sh SCRATCH SIDECAR}
SC=${2:?}
GEN="$F/circuits/quadcert/Gen/E2"
mkdir -p "$S/bitcones" "$GEN"

# One pass for all three cones, as `gen_all_loops.sh` does -- a dump per assertion would respawn
# cargo and re-parse the sidecar each time.
if [ ! -s "$S/bitcones/index.json" ]; then
  DUMP_CONES="$S/bitcones" DUMP_CONES_PATHS=e_eq,rx_eq,nmsinv \
    cargo run -q --release --manifest-path "$R/Cargo.toml" \
    --example meaning_gen -p compile-compiler -- "$SC" /dev/null
fi

emit() {
  local tag=$1 thm=$2 kind=$3 mod=$4
  local cone
  cone=$(ls "$S/bitcones/${tag}"*.json 2>/dev/null | head -1)
  if [ -z "$cone" ]; then
    echo "  $mod: no cone matching ${tag}* in $S/bitcones" >&2; return 1
  fi
  if python3 "$F/tools/gen_bitsum_meaning.py" "$cone" "$thm" "$kind" > "$GEN/$mod.lean.new" \
       2>"$S/bitcones/$mod.err"; then
    mv "$GEN/$mod.lean.new" "$GEN/$mod.lean"
    echo "  $mod  <- $(basename "$cone")  ($thm, $kind)"
  else
    rm -f "$GEN/$mod.lean.new"
    echo "  $mod FAILED: $(head -1 "$S/bitcones/$mod.err" | cut -c1-100)" >&2
    return 1
  fi
}

# Write to `.new` and move only on success, so a failure cannot leave the tree emptier than it
# found it -- the mistake that emptied `Gen/E2` when the merge driver cleared before writing.
bad=0
emit e_eq    bitsum_e_eq    eq  E2BitSumE   || bad=$((bad+1))
emit rx_eq   bitsum_rx_eq   eq  E2BitSumRx  || bad=$((bad+1))
emit nmsinv  bitsum_nmsinv  inv E2BitSumNms || bad=$((bad+1))
echo "gen_all_bitsums: $((3 - bad))/3 emitted"
[ "$bad" -eq 0 ]
