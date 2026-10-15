#!/bin/bash
# Regenerate one circuit's `Gen/` tree: compile the circuit, emit the certificate modules, decode
# the committed LFC2 bytes into Lean, and install the result.
#
# This exists because the sequence is four steps with long argument lists, and pasting them into a
# terminal is how they get mangled -- a wrapped line once left `cargo run ... --` on one line and
# `/tmp/s2 --field=p256` on the next, so the example ran with no arguments and bash tried to
# execute `/tmp/s2`.
#
# Both stages matter and are easy to half-run:
#
#   stage 1  `*_artifacts`   compiles the circuit, writes <c>.lfc2 / <c>.sidecar / manifest.txt,
#                            and emits the cert modules under OUT/lean/Gen/<Name>/
#   stage 2  `lfc2_to_lean`  decodes those committed bytes straight into
#                            circuits/quadcert/Gen/<Name>/ -- the artifact, commitment and parse
#                            chain
#
# Running stage 1 with `--no-artifact` (or skipping stage 2) leaves a tree whose `raw` is a
# self-contained literal: no `raw_from_bytes`, no `<Name>Commitment`. That builds, and every
# structural proof above it builds, but the three modules that tie the proofs to the *committed
# bytes* -- `S2Sound.assertions_zero_of_bytes`, `S2Bytes`, `S2EndToEnd` -- cannot. That is what
# the p256 tree was in, and the failure surfaced 64 modules into a build as an unknown identifier.
set -eu
F=$(cd "$(dirname "$0")/.." && pwd)
R=$(cd "$F/../rust" && pwd)

# Each target names the circuit it compiles, the field it compiles over, and the `Gen/` tree it
# installs into.  `sha256-p256` and `ecdsa2` are the two halves of the deployed mdoc proof.
TARGET=${1:?usage: regen_artifact.sh sha256-p256|sha256-gf2|ecdsa2 [SCRATCH]}
case "$TARGET" in
  sha256-p256|p256)
    NAME=Sha256Blk; FIELD=p256;    CRATE=circuits-sha256; EX=sha256_artifacts; BLOB=sha256 ;;
  sha256-gf2|gf2_128)
    NAME=Sha256Gf2; FIELD=gf2_128; CRATE=circuits-sha256; EX=sha256_artifacts; BLOB=sha256 ;;
  ecdsa2)
    NAME=Ecdsa2;    FIELD=p256;    CRATE=circuits-ecdsa2; EX=ecdsa2_artifacts; BLOB=ecdsa2 ;;
  *) echo "regen_artifact.sh: unknown target '$TARGET'" >&2
     echo "  expected one of: sha256-p256  sha256-gf2  ecdsa2" >&2; exit 1 ;;
esac
S=${2:-/tmp/regen-$NAME}
GEN="$F/circuits/quadcert/Gen/$NAME"

echo "regen_artifact: $NAME ($TARGET) over $FIELD, scratch $S"
rm -rf "$S"; mkdir -p "$S"

# The pin guards the one assumption this script rests on: that emitting the artifact half changes
# *which* modules come out, not the circuit. If the ids still match, every node id in the bridge
# layer survives and only the Gen tree is rebuilt. If they do not, the run stops here rather than
# renumbering 45 MB of generated bridge out from under proofs that name nodes.
PINS="$F/circuits/quadcert/CIRCUIT_PINS.txt"
KEY=$(echo "$TARGET" | sed 's/^p256$/sha256-p256/; s/^gf2_128$/sha256-gf2/')
if [ -r "$PINS" ]; then
  # Match the pin line for this target by name, so adding a second circuit cannot
  # silently check the first one's id.
  case "$KEY" in
    sha256-p256) PAT='sha256_block/p256' ;;
    sha256-gf2)  PAT='sha256_block/gf2_128' ;;
    ecdsa2)      PAT='ecdsa2' ;;
  esac
  PIN=$(grep "$PAT" "$PINS" 2>/dev/null | grep -o '[0-9a-f]\{64\}' | head -1 || true)
  [ -n "${PIN:-}" ] && export EXPECT_CIRCUIT_ID="$PIN" \
    && echo "regen_artifact: pinned to ${PIN:0:16}…"
  [ -z "${PIN:-}" ] && echo "regen_artifact: no pin recorded for $KEY" >&2
fi

cd "$R"
# `ecdsa2_artifacts` takes only OUT_DIR; the sha256 one also takes a field.
if [ "$CRATE" = circuits-sha256 ]; then
  cargo run --release -p "$CRATE" --example "$EX" -- "$S" "--field=$FIELD"
else
  cargo run --release -p "$CRATE" --example "$EX" -- "$S"
fi

# Clear the old tree *before* stage 2, not after: `lfc2_to_lean` writes its half straight into
# `Gen/$NAME`, so clearing afterwards would delete exactly what it just produced.  The two stages
# emit complementary halves into the same directory -- stage 2 the artifact, commitment and parse
# chain, stage 1 the node tables and cert modules -- and only stage 1's go through the scratch
# dir.  Clearing first also drops modules a previous run emitted and this one does not; a stale
# `.lean` with no importer is still built by `leanseq`.
rm -rf "$GEN"
mkdir -p "$GEN"

cargo run --release -p core-proto --example lfc2_to_lean -- \
  "$FIELD" "$S/$BLOB.lfc2" "$F/circuits/quadcert" "$NAME"
cp -r "$S/lean/Gen/$NAME/." "$GEN/"

# `Gen/Ecdsa2` has a *third* producer.  `Ecdsa2Meaning.lean` -- the meaning lemmas for every
# assertion whose cone expands outright (`valid_index`, `slice_x/y`, `is_on_curve`, `ax_zero`,
# the inverses) -- comes from `meaning_gen`'s default mode, not from either stage above.  Nothing
# ran it, so it had never been built in this tree; and since this script clears `Gen/$NAME`,
# running it by hand beforehand would not have survived the next regen.  `E2Digits` and
# `E2Small` both import it, so without it the whole ECDSA bridge stops at its first module.
# `Gen/Sha256Blk` has one too.  `Sha256BlkEdges.lean` -- the base node tables the `S2Edges*`
# bridges alias (`zOfW`, `zOfS`, `zOf6`, `zOf7`, `bitOfB`, `assertOfB`) -- comes from
# `meaning_gen`'s `EMIT_EDGES` mode.  Those tables were hand-maintained and went stale on the last
# recompile (63 of 64 `zOf6` bases wrong); the generator re-derives them by unification and
# refuses to emit unless the bridges' index formulas still reproduce every cone.
if [ "$TARGET" = sha256-p256 ] || [ "$TARGET" = p256 ]; then
  EMIT_EDGES=1 NAME=Sha256Blk \
    cargo run -q --release -p compile-compiler --example meaning_gen -- \
    "$S/$BLOB.sidecar" "$GEN/Sha256BlkEdges.lean"
fi

if [ "$TARGET" = ecdsa2 ]; then
  NAME=Ecdsa2 SUPPORT=Bridge.Ecdsa2.E2Meaning \
    cargo run -q --release -p compile-compiler --example meaning_gen -- \
    "$S/$BLOB.sidecar" "$GEN/Ecdsa2Meaning.lean"
fi

echo "regen_artifact: $(ls "$GEN" | wc -l) modules in Gen/$NAME"
grep -E '^(circuit_id|lfc2_root|lfc2_bytes|nassertions)' "$S/manifest.txt" || true
echo "regen_artifact: next -> tools/leanseq quadcert 36 '^Gen\\.$NAME\\.'"
