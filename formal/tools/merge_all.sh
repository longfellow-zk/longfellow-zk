#!/bin/bash
# Batch the per-lemma loop and mux files into the `Gen/E2` modules the bridges import.
#
# This driver was missing.  `gen_loop_meaning.py` and `gen_mux_meaning.py` each emit one
# self-contained module per lemma -- the right unit to generate and debug, the wrong unit to
# build, since every module pays the `import Mathlib` floor (measured: 1 lemma 20 s, 6 lemmas
# 24 s).  `merge_loops.py` and `merge_muxes.py` do the batching but take an explicit file list,
# and nothing called them, so `Gen/E2/E2LoopB*.lean` was never produced.
#
# That mattered beyond build cost: `gen_all_muxes.sh` reads each round's chosen mux triple back
# out of the merged loop modules rather than re-deriving it, precisely so the loop and mux lemma
# families cannot disagree about which triple a round uses.
#
# **The module names and batch count are read out of `gen_loop_ok.py`, not chosen here.**  That
# file emits the import list for the bridge, so it is what decides that there are 96 loop
# batches named `E2LoopB00..95` and 16 mux batches named `E2MuxM00..15`.  Guessing instead
# produced `E2Loop0..15` at 48 lemmas a batch, which merged all 768 lemmas correctly and still
# left every import dangling.
set -u
F=$(cd "$(dirname "$0")/.." && pwd)
S=${1:?usage: merge_all.sh SCRATCH}
GEN="$F/circuits/quadcert/Gen/E2"
mkdir -p "$GEN"

# `[f"import quadcert.Gen.E2.E2LoopB{k:02d}" for k in range(96)]` -> `E2LoopB 2 96`
scheme() {
  # `E2LoopB`/`E2MuxM` are named by `gen_loop_ok.py`; `E2BitB` by `gen_rest.py`.
  local from="$F/tools/gen_loop_ok.py"
  [ "$1" = E2BitB ] && from="$F/tools/gen_rest.py"
  python3 - "$from" "$1" <<'PY'
import re, sys
src, want = open(sys.argv[1]).read(), sys.argv[2]
m = re.search(r'f"import quadcert\.Gen\.E2\.(' + want + r')\{k:(\d+)d\}"\s*for k in range\((\d+)\)', src)
if not m:
    sys.exit(f"gen_loop_ok.py has no import pattern for {want}")
print(m.group(1), m.group(2), m.group(3))
PY
}

merge_family() {
  local kind=$1 script=$2 want=$3 lister=$4
  read -r prefix width count < <(scheme "$want") || exit 1
  local files n
  mapfile -t files < <($lister)
  n=${#files[@]}
  if [ "$n" -eq 0 ]; then
    echo "merge_all: no $kind lemmas in $S -- skipping"; return 0
  fi
  if [ $(( n % count )) -ne 0 ]; then
    echo "merge_all: $n $kind lemmas do not divide into $count batches" >&2; exit 1
  fi
  local per=$(( n / count )) k=0
  rm -f "$GEN/${prefix}"*.lean
  while [ $k -lt "$count" ]; do
    local name; name=$(printf "%s%0${width}d" "$prefix" "$k")
    python3 "$F/tools/$script" "$name" "${files[@]:$((k * per)):$per}" > "$GEN/${name}.lean"
    k=$((k + 1))
  done
  echo "merge_all: $kind -> $count modules ${prefix}$(printf "%0${width}d" 0)..$(printf "%0${width}d" $((count-1))), $n lemmas, $per each"
}

order_loops() { for C in wx wy wz; do for I in $(seq 0 255); do
  f="$S/loops/${C}_${I}.lean"; [ -s "$f" ] && echo "$f"; done; done; }
order_muxes() { for I in $(seq 0 255); do
  f="$S/muxes/mux_${I}.lean"; [ -s "$f" ] && echo "$f"; done; }
order_bits()  { for I in $(seq 0 255); do
  f="$S/bits/bits_${I}.lean"; [ -s "$f" ] && echo "$f"; done; }

# The wrongly-named modules a previous guess left behind would still be built by `leanseq`.
rm -f "$GEN"/E2Loop[0-9]*.lean "$GEN"/E2Mux[0-9]*.lean

merge_family loops merge_loops.py E2LoopB order_loops
merge_family muxes merge_muxes.py E2MuxM  order_muxes
merge_family bits  merge_bits.py  E2BitB  order_bits
