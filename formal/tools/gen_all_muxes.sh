#!/bin/bash
# Generate every round's mux meaning lemma, batched into modules.
#
# 256 rounds. The three wire ids per round are read out of the *generated loop lemmas* rather
# than searched for again: `gen_loop_meaning.py` already committed to a particular triple (and
# for round 255 had to be forced to, since `addE zero mux` is symmetric in X), so re-deriving
# them here could silently pick a different one and the two lemma families would not compose.
# Reading them back is the only way the association is guaranteed to match.
set -u
R=/Users/abhi/Projects/longfellow-zk/rust
F=/Users/abhi/Projects/longfellow-zk/formal
S=${1:?usage: gen_all_muxes.sh SCRATCH SIDECAR}
SC=${2:?}
mkdir -p "$S/muxes"

python3 - "$F" "$S" <<'PY'
import re, glob, collections, json, sys
F, S = sys.argv[1], sys.argv[2]
head = re.compile(r'theorem loop_w([xyz])_(\d+) \(inputs(.*?):= by', re.S)
mux = re.compile(r'⟨interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+), '
                 r'interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+), '
                 r'interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+)⟩ '
                 r': ProjectivePoint F\) params\)')
rounds = collections.defaultdict(dict)
for f in glob.glob(F + '/circuits/quadcert/Gen/E2/E2Loop*.lean'):
    for m in head.finditer(open(f).read()):
        g = mux.search(re.sub(r'\s+', ' ', m.group(3)))
        rounds[int(m.group(2))][m.group(1)] = tuple(g.groups()) if g else None
bad = [i for i, d in rounds.items()
       if len(d) != 3 or None in d.values() or len(set(d.values())) != 1]
assert not bad, f"rounds whose three coordinates disagree on the mux triple: {sorted(bad)}"
assert len(rounds) == 256, f"expected 256 rounds, found {len(rounds)}"
json.dump({str(k): next(iter(v.values())) for k, v in rounds.items()},
          open(S + '/muxwires.json', 'w'))
print(f"read mux triples for {len(rounds)} rounds")
PY

ok=0; bad=0
for I in $(seq 0 255); do
  out="$S/muxes/mux_${I}.lean"
  [ -s "$out" ] && { ok=$((ok+1)); continue; }
  W=$(python3 -c "import json,sys; print(','.join(json.load(open('$S/muxwires.json'))['$I']))")
  DUMP_NODE="$W" cargo run -q --release --manifest-path $R/Cargo.toml \
    --example meaning_gen -p compile-compiler -- "$SC" /dev/null 2>/dev/null > "$S/muxes/c.jsonl"
  if python3 $F/tools/gen_mux_meaning.py "$S/muxes/c.jsonl" "mux_${I}" \
       > "$out" 2>"$S/muxes/${I}.err"; then
    ok=$((ok+1))
  else
    bad=$((bad+1)); rm -f "$out"
    echo "FAILED mux[$I]: $(head -1 "$S/muxes/${I}.err" | cut -c1-100)"
  fi
done
echo "TOTAL matched=$ok failed=$bad"
