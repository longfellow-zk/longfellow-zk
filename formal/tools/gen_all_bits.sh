#!/bin/bash
# Generate every round's bit-table meaning lemma, one per round covering all three tables.
#
# The wire ids come out of the *generated bit-sum lemmas* (`E2BitSumE`, `E2BitSumRx`,
# `E2BitSumNms`), whose statements list the 256 opaque wires in `bitsLE` order. Reading them back
# is what guarantees the two families compose: a wire found any other way could be a different
# node with the same value.
set -u
R=/Users/abhi/Projects/longfellow-zk/rust
F=/Users/abhi/Projects/longfellow-zk/formal
S=${1:?usage: gen_all_bits.sh SCRATCH SIDECAR}
SC=${2:?}
mkdir -p "$S/bits"

python3 - "$F" "$S" <<'PY'
import re, json, sys
F, S = sys.argv[1], sys.argv[2]
out = {}
for tag, f in (('e', 'E2BitSumE'), ('rx', 'E2BitSumRx'), ('nms', 'E2BitSumNms')):
    src = re.sub(r'\s+', ' ', open(f'{F}/circuits/quadcert/Gen/E2/{f}.lean').read())
    m = re.search(r'ECDSA2\.bitsLE \[(.*?)\] ', src)
    ids = [int(x) for x in re.findall(
        r'interpDag \(raw\.toDag \(Ecdsa2\.consts F\)\) inputs (\d+)', m.group(1))]
    assert len(ids) == 256, f'{tag}: {len(ids)} wires'
    out[tag] = ids
json.dump(out, open(S + '/bitwires.json', 'w'))
print('read 3 x 256 bit wires')
PY

ok=0; bad=0
for I in $(seq 0 255); do
  out="$S/bits/bits_${I}.lean"
  [ -s "$out" ] && { ok=$((ok+1)); continue; }
  W=$(python3 -c "
import json; b=json.load(open('$S/bitwires.json'))
print(f\"{b['e'][$I]},{b['rx'][$I]},{b['nms'][$I]}\")")
  DUMP_NODE="$W" cargo run -q --release --manifest-path $R/Cargo.toml \
    --example meaning_gen -p compile-compiler -- "$SC" /dev/null 2>/dev/null > "$S/bits/c.jsonl"
  if python3 $F/tools/gen_bit_meaning.py "$S/bits/c.jsonl" "bits_${I}" \
       > "$out" 2>"$S/bits/${I}.err"; then
    ok=$((ok+1))
  else
    bad=$((bad+1)); rm -f "$out"
    echo "FAILED bits[$I]: $(head -1 "$S/bits/${I}.err" | cut -c1-100)"
  fi
done
echo "TOTAL matched=$ok failed=$bad"
