# Legacy sumcheck

`runtime-sumcheck` implements the historical round-major, two-hand protocol.
`runtime-sumcheck-ng` remains a separate single-hand implementation. Both now use
independent verifier-data, symbolic-verifier, and ZK constraint-compiler modules.

The numerical prover advances the main transcript and returns the proof plus
local `VerifierData`: one interpolation coefficient triple per round and hand,
each layer's `alpha` and bound wiring scalar, the final input-combination
challenge, and the final dense input weights. Coefficients are computed once;
the final weights move into the input relation. No intermediate dense vectors
are cached across layers.

`derive_verifier_data` independently computes that data from the circuit, proof,
and transcript. Success validates shape and derives data; it does not establish
acceptance. `symbolic::verify` is pure and constructs acceptance relations over
logical sumcheck pads and inputs. It knows no transcript, circuit, commitment
coordinates, or Ligero types. The numerical verifier evaluates these relations
with revealed inputs and pads. `runtime-zk::constraint_compiler` lowers the same
relations to sparse Ligero constraints and endpoint-pad product constraints.
Protocol codecs and pad geometry live in `runtime-proto::sumcheck`.

ZK proof bytes, transcript scheduling, pad sampling, and stored RFC compatibility
are preserved. The bare numerical prover/verifier now also consume the final
input-combination challenge that previously belonged only to the ZK symbolic
pass. The revealed-input verifier uses that same combined-input equation in
place of its former two separate hand checks. Their return-data API replaces `SumcheckProofAux` with `VerifierData`.
The old `Claims` / `SumcheckProofAux` state types and the ZK symbolic entry point
have been replaced. Pad sampling is `pad::sample`, and coordinate layouts come
from the protocol geometry. The obsolete physical-coordinate expression helper
has been removed. There are no transcript clones, observers, or explicit `drop`
calls in the new flow. Sumcheck random values are called pads; mask refers to
Ligero mask rows.

Validation from `rust/`:

```sh
cargo test --workspace --release
cargo clippy --no-deps -p runtime-sumcheck -p runtime-zk --all-targets -- -D warnings -A clippy::chunks_exact_to_as_chunks
```

The lint exception is confined to an existing style diagnostic in the unchanged
legacy dense-folding helper. Tests compare prover/independently derived data,
pre-refactor proof and transcript fingerprints, independent numerical and symbolic
equations, sparse lowering over prime/binary fields, zero-round/zero-layer
circuits, public/private input splits, zero weights, constant-only constraints,
malformed local data, endpoint-product tampering, and legacy pad-coordinate order.

Latest full release run: **565 passed, zero failed, 23 ignored by default**.
The [complete log](../../experiments/mldsa/results/legacy-relations-release-tests.log)
includes historical mdoc compatibility, legacy RFC vectors, fresh round trips,
and NG regression tests.
