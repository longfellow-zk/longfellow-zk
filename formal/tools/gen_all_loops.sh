#!/bin/bash
# Generate every loop-round meaning lemma, batched into modules.
#
# 768 assertions (256 rounds x 3 coordinates). Each needs its cone dumped from the sidecar, the
# mux boundary found by search, and the modulo-p correction computed; then they are batched,
# because a module's Mathlib import dominates a single lemma's cost (1 lemma 20 s, 6 lemmas 24 s).
#
# The cones are dumped **once**. The previous version ran `DUMP_CONE=... DUMP_IDX=...` inside the
# loop, which spawned 768 cargo processes and re-parsed the sidecar in every one of them;
# `DUMP_CONES` walks all assertions in a single pass and writes byte-identical JSON, so
# `slice_wx_0.json` here is exactly what `DUMP_CONE=slice_wx DUMP_IDX=0` used to print.
set -u
F=$(cd "$(dirname "$0")/.." && pwd)
R=$(cd "$F/../rust" && pwd)
S=${1:?usage: gen_all_loops.sh SCRATCH SIDECAR}
SC=${2:?}
mkdir -p "$S/loops" "$S/cones"

# `index.json` doubles as the sentinel: present means the dump already ran for this scratch dir.
if [ ! -s "$S/cones/index.json" ]; then
  DUMP_CONES="$S/cones" DUMP_CONES_PATHS=slice_wx,slice_wy,slice_wz \
    cargo run -q --release --manifest-path "$R/Cargo.toml" \
    --example meaning_gen -p compile-compiler -- "$SC" /dev/null
fi

ok=0; bad=0
for C in wx wy wz; do
  for I in $(seq 0 255); do
    out="$S/loops/${C}_${I}.lean"
    [ -s "$out" ] && { ok=$((ok+1)); continue; }
    cone="$S/cones/slice_${C}_${I}.json"
    if [ ! -s "$cone" ]; then
      bad=$((bad+1)); echo "MISSING cone $C[$I] ($cone)"; continue
    fi
    if python3 "$F/tools/gen_loop_meaning.py" "$cone" "loop_${C}_${I}" "$C" \
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

# Reconcile rounds whose three coordinates chose different mux triples.
#
# `gen_loop_meaning.py` searches per coordinate and stops at the first triple that validates, so
# nothing makes the three agree.  They must: `gen_all_muxes.sh` reads the triple back out of the
# loop lemmas and the mux lemma has to name the *same* term, or the two families will not compose
# in Lean.  The degenerate first round is where they diverge -- with the accumulator the constant
# `(0, 1, 0)`, `addE zero mux = mux` and each coordinate can stop at a different representation
# of the same point.
#
# Doing it here rather than leaving it to the mux stage keeps the failure next to its cause.
# `find_mux.py` searches all three cones at once; `MUX=` then forces its answer.
python3 - "$F" "$S" <<'PY' > "$S/disagree.txt"
import re, sys, collections
F, S = sys.argv[1], sys.argv[2]
mux = re.compile(r'\u27e8interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+), '
                 r'interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+), '
                 r'interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+)\u27e9 '
                 r': ProjectivePoint F\) params\)')
rounds = collections.defaultdict(dict)
for c in ("wx", "wy", "wz"):
    for i in range(256):
        try: src = open(f"{S}/loops/{c}_{i}.lean").read()
        except FileNotFoundError: continue
        g = mux.search(re.sub(r'\s+', ' ', src))
        rounds[i][c] = g.groups() if g else None
for i, d in sorted(rounds.items()):
    if len(d) == 3 and (None in d.values() or len(set(d.values())) != 1):
        print(i)
PY

nd=$(wc -l < "$S/disagree.txt" | tr -d ' ')
if [ "$nd" -gt 0 ]; then
  echo "reconciling $nd round(s) whose coordinates disagree on the mux triple"
  while read -r I; do
    [ -n "$I" ] || continue
    if ! T=$(python3 "$F/tools/find_mux.py" "$S/cones" "$I"); then
      echo "  round $I: no common triple -- left as generated"; continue
    fi
    good=0
    for C in wx wy wz; do
      MUX="$T" python3 "$F/tools/gen_loop_meaning.py" "$S/cones/slice_${C}_${I}.json" \
        "loop_${C}_${I}" "$C" > "$S/loops/${C}_${I}.lean.new" 2>/dev/null \
        && mv "$S/loops/${C}_${I}.lean.new" "$S/loops/${C}_${I}.lean" && good=$((good+1)) \
        || rm -f "$S/loops/${C}_${I}.lean.new"
    done
    echo "  round $I: MUX=$T -> $good/3 regenerated"
  done < "$S/disagree.txt"
else
  echo "all rounds agree on their mux triple"
fi
