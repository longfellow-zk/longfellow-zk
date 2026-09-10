#!/bin/bash
# Generate every loop-round meaning lemma, batched into modules.
#
# 768 assertions (256 rounds x 3 coordinates). Each needs its cone dumped from the sidecar, the
# mux boundary found by search, and the modulo-p correction computed; then they are batched,
# because a module's Mathlib import dominates a single lemma's cost (1 lemma 20 s, 6 lemmas 24 s).
set -u
R=/Users/abhi/Projects/longfellow-zk/rust
F=/Users/abhi/Projects/longfellow-zk/formal
S=${1:?usage: gen_all_loops.sh SCRATCH SIDECAR}
SC=${2:?}
BATCH=48
mkdir -p "$S/loops"
ok=0; bad=0
for C in wx wy wz; do
  for I in $(seq 0 255); do
    out="$S/loops/${C}_${I}.lean"
    [ -s "$out" ] && { ok=$((ok+1)); continue; }
    DUMP_CONE=slice_$C DUMP_IDX=$I cargo run -q --release --manifest-path $R/Cargo.toml \
      --example meaning_gen -p compile-compiler -- "$SC" /dev/null 2>/dev/null > "$S/loops/c.json"
    if python3 $F/tools/gen_loop_meaning.py "$S/loops/c.json" "loop_${C}_${I}" "$C" \
         > "$out" 2>"$S/loops/${C}_${I}.err"; then
      ok=$((ok+1))
    else
      bad=$((bad+1)); rm -f "$out"
      echo "FAILED $C[$I]: $(head -1 "$S/loops/${C}_${I}.err" | cut -c1-90)"
    fi
  done
  echo "== $C done: $ok matched, $bad failed"
done
echo "TOTAL matched=$ok failed=$bad"
