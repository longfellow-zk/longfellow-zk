# Witness selection

`runtime::v2::witness_selection` wraps joint Polygero between commitment and frontend
reduction. The v2 ZK joint wrapper invokes it for standalone proofs and for mdoc's
GF128 and P256 participants. Applications use the v2 ZK wrapper. It contains no
circuit, sumcheck, or packing implementation. `prover.rs` and `verifier.rs` own
their respective role operations. `witness_selection.rs` and `fields.rs` own the
shared layout and fingerprint equations; `transcript.rs` owns v2 framing,
coefficient sampling and response binding.

For a frontend's existing field-cell vector `w`, the protocol appends two fresh
private masks `m₁,m₂`. `witness_count` gives the augmented backend count; frontend
cell indices stay unchanged. The masks are excluded from `w`, do not reuse any
packing or sumcheck randomness, and never become circuit inputs.

The transcript statement already fixes every field's layout. The draw that
follows the joint `Commitment` message ends its node and reads two independent
uniform vectors per field from that node's SHA-256 PRF stream. There is no
prover message between the vectors or fields. Prime-field rejection sampling
extends that reader. The responses are

```
t₁ = m₁ + dot(a₁,w)
t₂ = m₂ + dot(a₂,w).
```

Each field then sends its `FingerprintResponse` before control returns to the
frontend. In mdoc this precedes
the prime-field sumcheck as well as the binary sumcheck. Responses occupy
96 bytes across those two fields; masks and coefficients are not serialized.

The returned prover and verifier states retain private backend handles, the
coefficients, the responses and the stamp of the session they were created on;
they do not hold the transcript, which the zk joint wrapper owns. Their
crate-private `finish` checks the stamp, so a state completes only on its own
transcript, and takes no replacement root. Given every field's later affine
statements, it rejects any derived on another session, appends
`dot(aⱼ,w) + mⱼ - tⱼ = 0`, and hands the system to joint Polygero, which draws
the batching weights itself (DESIGN.md I5, I8). Frontend equations cannot
address the dedicated mask cells. Consuming statements avoids copying their
sparse arrays. The raw witness is never copied: the backend encodes its rows
from a borrow, and the witness is released once the responses are formed; the
retained state contains coefficients and the encoded backend.

Field lists use recursive typed tuples ending in `()`, so one, two, repeated,
or more fields use the same code. Fields need canonical serialization and
uniform sampling. A field's identity is its type's registered `FieldID`, and
its layout is the statement's: `Field::new(param, domain)` takes no identity,
and witness selection absorbs nothing of its own (DESIGN.md I2). No packing
capability or generic sampling fallback is required.

This is an intermediate protocol. Its early responses fix targets and its
later backend check authenticates them. The enclosing complete-proof encoder
owns the mandatory final transcript seal, including these responses and the
terminal authentication data.

The [formal module](../../../../../formal/witness-selection/README.md) separates the
fingerprint collision charge from fixed-witness frontend soundness and the
remaining Polygero extraction errors. The
[numbered-strand analysis](../../../../../formal/transcript-v2/README.md) models
the SHA-256 node and counter-indexed PRF queries, segmented byte reads and final
seal. Its query accounting retains the original adversarial SHA log and
commitment cut. Soundness assumes the stated joint successful-sampling law for
the physical role readers; concrete Rust sampler refinement remains a separate
implementation obligation.
The [current mdoc composition](../../../../../formal/lfzk-v2/README.md)
combines selection with both frontend reductions and joint Polygero in its
one-SHA extraction theorem. Its separate joint-view zero-knowledge theorem
covers the complete proof or failure and both observer query traces, including
the early fingerprint responses.
