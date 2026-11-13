# ZK V2

`runtime::v2::zk` composes projective sumcheck, authenticated input packing and
nonrecursive Polygero. `runtime::v1::zk` retains the separate deployed protocol.
`ZkProver`, `ZkVerifier`, `ZkContext` and `ZkProverCommitment` provide standalone
proofs. `joint::JointParam` owns early witness selection and the final joint
authentication for standalone and application proofs. `joint::CircuitParticipant`
supplies circuit reductions to that wrapper. Prover and verifier orchestration
stay in separate files; layout and constraint arithmetic are shared.

The [Lean development](../../../../formal/lfzk-v2/README.md) proves extraction
soundness and complete joint-view statistical zero knowledge for the current
MAC-free mdoc composition under its stated trusted circuit/arithmetic setup,
sampling and ideal-oracle assumptions. The witness-free simulator covers public
setup, the complete proof or failure, and both observer query traces, with error
at most `(Qpre+Qpost)/2^256`. Its proof separates one statistical commitment-hiding
step from an exact joint frontend/backend coin change. Canonical proof and query
encodings are modeled; Rust correspondence is checked by source audit and tests.
Soundness assumes the joint successful-sampling law for the physical role
readers. Privacy preserves those readers and their failures without requiring
uniform verifier challenges; it assumes independent uniform private coins.

## Commitment and field participants

`ZkContext::new(domain)` obtains its field directly from the ordered interpolation
domain. Parameters and participants use that same field; no separate arithmetic
instance can be attached. Joint protocol handles own the commitment and transcript
through receipt, frontend reductions and authentication. Their `transcript()`
accessor exposes only `TranscriptRef`, which permits protocol operations without
replacing, resetting or finalizing the owned session. Successful completion
returns the original transcript for the complete-proof seal.
`CircuitParticipant::new` derives immutable proof geometry, witness layout and
Polygero parameters. `prepare` validates and packs typed private inputs, samples
sumcheck pads and returns the witness and owned reduction state. Binary source
inputs are Boolean; prime-field inputs remain field elements.

`CircuitGeometry` contains the circuit reduction and commitment dimensions.
The standalone `ZkProofGeometry` adds the context of its actual joint participant
list; application envelopes supply their own joint context. Preparing a circuit
still validates its selected field, without constructing a singleton context.

Each participant binds its packing interpretation and circuit-composition layout
before the shared root. `JointParam` accepts recursive `(SelectedField, Tail)`
tuples ending in `()`, preserving each field's types. It uses the sibling
witness-selection protocol to append two fresh private masks per field,
commit the augmented vectors, and bind all masked fingerprints before any
frontend challenges. Circuit geometry includes those backend cells automatically;
packing and logical circuit inputs retain their original layout.
All participants share `(k,s,n,t)`, one
salted tuple-column Merkle tree and one query set. A standalone proof uses the
same wrapper with one participant. Shared queries do not imply independent
failure events; the per-field residual budgets add.

After commitment, each participant runs its circuit and packing reduction.
`prove` and `reduce` return an affine `LinearStatement`. Returning that statement
is not an acceptance decision: the caller must consume the opaque joint handle
to authenticate the frontend and fingerprint equations together. Standalone
verification receives the commitment and fingerprints internally before its
circuit reduction. All statements are bound
before backend batching challenges, and every field's responses precede the
shared queries. The verifier checks the received root and commitment context.

Polygero retains encoded rows without copying the original witness. Proving
consumes the commitment state, releasing the rows and tree when finished.
Opened values remain packed by row, in transcript query order within each row.
The committed row order is `u, m`, witness rows, then `fstar`; polynomial batching
indices match all rows before `fstar`. All masks and serialized field elements
use the ambient field. H and Z occupy oracle prefixes starting at K, of lengths
K+S and 2K; the verifier interpolates Z back to the logical witness points and
sums them. T controls both openings and row masks.

## Same-field circuit composition

`CircuitParticipant::with_circuits` combines the supplied circuits in one
layered sumcheck. They share the public prefix and read prefixes of one input
array as wide as the widest circuit.
`prove_circuits` and `reduce_circuits` take that ordered circuit list and the
same public inputs. The prover supplies one private source vector, packed and
committed once. All circuit IDs and the common public values bind before sumcheck.

The input array is shared. Intermediate layers concatenate each active
circuit's wires in decreasing depth order, breaking ties by the original
list index, without padding between circuits. Sparse
quadratic, linear and constant streams retain local indices; their slices of
the global arrays supply the offsets. At the input boundary every fragment's
input offset is zero, so their contributions accumulate into the same input
weights; a narrower circuit contributes only to its prefix.

`CircuitParticipant::with_virtual_inputs` reserves the last entries of the
shared input array as virtual inputs. Each proof defines them as affine
functions `c0 + c1 * x[source]` of committed private inputs (`VirtualInputs`);
both roles derive the definitions, and they are never absorbed. The prover
appends their values to the input array. `compile_packed` substitutes them
like public inputs: each constant moves to the right-hand side and each
linear part joins its source input's weight, so virtual inputs are never
committed. The primary circuit must end before the virtual suffix and so
cannot read it; the other circuits may. `prove_virtual` and `reduce_virtual`
take the definitions; `prove_circuits` and `reduce_circuits` use none.

Shorter circuits join later, aligned at their inputs. New zero-output claims
receive fresh output weights. Each layer otherwise uses ordinary sumcheck over
one witness array and one coefficient array, with exactly two terminal claims
and one alpha challenge. The final weights already address the shared inputs,
so no input-claim pullback is needed. One packing reduction authenticates that
claim. Single-circuit callers use exactly the same implementation.

Geometry and shared-input counts are validated during preparation. Circuit
identities, input layouts, public counts and proof shapes are checked before
advancing the sumcheck transcript. Circuit evaluation checks all outputs and
assertions. The source compiler's unused-input checks and Boolean-input
contract are unchanged.

## Symbolic constraints and packing

Sumcheck algebra belongs to `runtime::v2::sumcheck::symbolic`. Numerical proving
and public reconstruction use the same symbolic builder, returning affine
constraints over logical inputs and pads. Each stage contributes one terminal
constraint, followed by the final input claim. Deriving these constraints alone
does not authenticate them.

Components are ordered by decreasing depth, preserving their supplied order at
equal depths. The protocol key is `(decreasing depth, increasing original
index)` in the transcript-bound circuit list, including duplicate circuit IDs.
Carried claim weights therefore extend in place as new outputs enter.
Every circuit output is a zero assertion at its global layer. Its fresh
coefficient shares that layer's assertion answer with the explicit quadratic
and linear assertions. Fragments add no queries. Only the current layer's terms
are contracted; the next layer receives the resulting dense claim weights.
Input-only circuits extend the final combine answer with their assertion
coefficients. A proof with no layers instead uses one input assertion block.

`constraint_compiler::compile_packed` substitutes the main public inputs and
maps logical pad positions into committed witness coordinates. It emits sparse
terminal rows and the dense source claim for the packing adapter. The adapter
produces two linear rows for trace-zero packing, or one direct row for degree
one. Degree-one packing introduces no masks, messages or sampling. All equations
use `sum_w A[c,w]*w + b[c] = 0`; coefficients, explicit zeros, duplicate terms
and constants are retained. The fresh sumcheck terminal scale makes the cross
pad and product cell linear in these rows, without backend product-copy checks.

Polygero binds each source circuit ID before its scalar and polynomial
challenges. The public inputs, commitment, sumcheck messages and packing
responses already precede that boundary on the same transcript. This handoff
adds no query or proof bytes. Sparse A/b encoding and term order are outside
this binding: both roles derive these rows locally. Standalone Polygero callers use `LinearStatement::new`, which hashes the
complete static system and exposes immutable coefficients and targets. Internal
frontends construct their derived rows from the already absorbed transcript;
challenge-derived coefficients are never absorbed.

`context.rs` derives layouts for both roles. The commitment context contains
only backend dimensions and the ordered field domains. Joint commit/receive
absorbs composition metadata internally before the fingerprint round, together
with the main circuit identity when the packing degree exceeds one. A
degree-one participant binds only its additional circuit IDs and layer widths
there; its main circuit ID first enters with the sumcheck statement, after the
fingerprint responses, so its fingerprint coefficients are not separated by
circuit ID. Soundness does not rely on that separation: sumcheck binds the ID
before its own challenges. Participant construction carries this metadata;
there is no separate frontend absorb call. Circuits
are trusted immutable metadata: the runtime absorbs their IDs without rehashing
them. Symbolic pad expressions end at constraint compilation. They are not
serialized, and no intermediate dense input-weight vectors are cached.

## Storage

A participant's value vector is `[private inputs | pads]`. By default every
value is a native cell of its own commitment. `CircuitParticipant::with_storage`
takes a `StorageMap` (`storage.rs`) that marks some values foreign: bits in the
binary commitment. The participant then derives its commitment layout from the
map.

- Mixed storage commits `[native private inputs | R | pads]`. Its frontend
  batches every layer and input equation into one linear claim
  `<w, v> = t` (`batching.rs`). A fresh nonzero `eta` and one masked message
  `mu = eta*<w_F, v_F> + R` split that claim (`split.rs`) into two parts:
  - a native row `eta*<w_N, v_N> - R + mu - eta*t = 0`, for this field's
    Polygero participant;
  - a modular claim `<eta*w_F, v_F> + R_bits = mu (mod p)` over foreign bit
    groups.
- Pure foreign storage commits nothing. The whole claim is modular, and its
  target is public.

The [foreign storage layer](../foreign/README.md) discharges modular claims.
Before the shared root, a split participant binds its circuit ID, its storage
map as runs, and R's bit group instead of the packing layout.

## Application and encoding

The mdoc application exposes `mdoc::v2::run_mdoc_prover` and
`mdoc::v2::run_mdoc_verifier`, with corresponding deterministic inner entry points.
It connects its hash and signature fields through the
[foreign storage layer](../foreign/README.md), which owns the cross-field
protocol, its round order and its reserved-input layout. The v2
ZK joint wrapper invokes the separate
[witness-selection protocol](../witness-selection/README.md), binding both fields'
masked fingerprints before either sumcheck, and automatically adds the
fingerprint affine equations to the frontend statements.

`packing_commitment.rs` connects the input-packing protocol to committed cells.
This crate builds without the `mdoc` feature.

Proof types and canonical codecs live in `runtime::v2::proto`, with the application
envelope under `mdoc::runtime::v2::proto`. Standalone ZK proofs use `LFV9` and
include the two masked fingerprint responses. Mdoc
proofs use `MDA7`, and the shared Polygero envelope uses `JPG2`.
Serialization writes backend data directly into the containing proof buffer.
V2 uses typed rounds over SHA-256 strands and a mandatory final seal owned by
the complete-proof encoder; nested circuit and backend bodies have no extra seals.
V1 encodings and transcripts are unchanged.

Tests under `tests/` cover single- and multiple-circuit proofs, binary packing and
prime-field direct inputs, shared input layouts, independent transcript replay,
malformed shapes, altered messages and commitment binding. The global dependency checker enforces protocol and role boundaries.
