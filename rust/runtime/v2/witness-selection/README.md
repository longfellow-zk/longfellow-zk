# Witness selection

`runtime::v2::witness_selection` wraps joint Polygero between commitment and frontend
reduction. The zk-v2 joint wrapper invokes it for standalone proofs and for mdoc's
GF128 and P256 participants. Applications use the zk-v2 wrapper. It contains no
circuit, sumcheck, or packing implementation. `prover.rs` and `verifier.rs` own
their respective role operations. `lib.rs` owns the shared layout and fingerprint
equations; `transcript.rs` owns v2 framing, coefficient sampling and response binding.

For a frontend's existing field-cell vector `w`, the protocol appends two fresh
private masks `m₁,m₂`. `witness_count` gives the augmented backend count; frontend
cell indices stay unchanged. The masks are excluded from `w`, do not reuse any
packing or sumcheck randomness, and never become circuit inputs.

After the joint commitment, one typed transcript round binds the commitment,
ordered field identities, public cell layouts, and fingerprint domain. It draws
two independent uniform vectors per field directly from the same SHAKE reader.
There is no prover message between the vectors or fields. Prime-field rejection
sampling extends that reader. The responses are

```
t₁ = m₁ + dot(a₁,w)
t₂ = m₂ + dot(a₂,w).
```

All responses bind before control returns to the frontend. In mdoc this precedes
the prime-field sumcheck as well as the binary sumcheck. Responses occupy
96 bytes across those two fields; masks and coefficients are not serialized.

The returned prover and verifier states retain private backend handles. When
given the frontend's later affine statements, they automatically append
`dot(aⱼ,w) + mⱼ - tⱼ = 0` before invoking Polygero. Frontend equations cannot
address the dedicated mask cells. Consuming statements avoids copying their
sparse arrays. The only temporary raw-witness copy is released after the early
exchange; the retained state contains coefficients and the encoded backend.

Field lists use recursive typed tuples ending in `()`, so one, two, repeated,
or more fields use the same code. Fields need canonical serialization and
uniform sampling. The trusted caller supplies the canonical field identity,
including its modulus. No packing capability or generic sampling fallback is
required.

This is an intermediate protocol. Its early responses fix targets and its
later backend check authenticates them. The enclosing complete-proof encoder
owns the mandatory final transcript seal, including these responses and the
terminal authentication data.

The [formal module](../../../../formal/witness-selection/README.md) separates the
fingerprint collision charge from fixed-witness frontend soundness and the
remaining Polygero extraction errors. The
[typed chain analysis](../../../../formal/transcript-v2/README.md) proves adaptive
query charging with a common `(Q+1)/2^256` link/seal exception. Correspondence
between the Rust encoding and samplers and the formal ideal model remains an
explicit obligation. The [current mdoc composition](../../../../formal/lfzk-v2/README.md)
combines this selection analysis with both frontend reductions and joint Polygero.
