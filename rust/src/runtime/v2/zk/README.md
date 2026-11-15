# ZK V2

`runtime::v2::zk` composes projective sumcheck, authenticated input packing and
nonrecursive Polygero. `runtime::v1::zk` retains the separate deployed protocol.
`ZkProver`, `ZkVerifier`, `ZkContext` and `ZkProverCommitment` provide standalone
proofs. `joint::JointParam` owns early witness selection and the final joint
authentication for standalone and application proofs. `joint::CircuitParticipant`
supplies circuit reductions to that wrapper. Prover and verifier orchestration
stay in separate files; layout and constraint arithmetic are shared.

The [Lean development](../../../../../formal/lfzk-v2/README.md) proves extraction
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
instance can be attached. The joint handles take the transcript by value at
commit or receive and own it through the frontend reductions and the
authentication; they have no public transcript accessor. A frontend reaches the
session only through a handle's crate-private `bound()`, after the fingerprint
responses (DESIGN.md I6). Successful completion returns the transcript for the
complete-proof seal.
`CircuitParticipant::new` derives immutable proof geometry, witness layout and
Polygero parameters. `prepare` validates and packs typed private inputs, samples
sumcheck pads and returns the witness and owned reduction state. Binary source
inputs are Boolean; prime-field inputs remain field elements.

`CircuitGeometry` contains the circuit reduction and commitment dimensions.
The standalone `ZkProofGeometry` adds the proof's one Polygero profile;
application envelopes supply their own joint geometry. Preparing a circuit
still validates its selected field.

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
circuit reduction. `JointProver::finish` and `JointVerifier::finish` take every
field's equations after its last frontend message and draw the backend
batching weights themselves, so no caller holds them (DESIGN.md I4); every
field's responses precede the shared queries. The verifier checks the received root.

Polygero retains encoded rows without copying the original witness. Proving
consumes the commitment state, releasing the rows and tree when finished.
Opened values remain packed by row, in transcript query order within each row.
The committed row order is `u, m`, witness rows, then `fstar`; polynomial batching
indices match all rows before `fstar`. All masks and serialized field elements
use the ambient field. H and Z occupy oracle prefixes starting at K, of lengths
K+S and 2K; the verifier interpolates Z back to the logical witness points and
sums them. T controls both openings and row masks.

## Same-field circuit composition

`CircuitParticipant::new(circuits, virtual_inputs, ..)` combines the supplied
circuits in one layered sumcheck; `circuits[0]` is the primary circuit. They
share the public prefix and read prefixes of one input array as wide as the
widest circuit. `prove` and `reduce` take the same ordered circuit list, which
must match the participant's circuit IDs, and the same public inputs. The
prover supplies one private source vector, packed and committed once. All
circuit IDs and the common public values bind before sumcheck.

The input array is shared. Intermediate layers concatenate each active
circuit's wires in decreasing depth order, breaking ties by the original
list index, without padding between circuits. Sparse
quadratic, linear and constant streams retain local indices; their slices of
the global arrays supply the offsets. At the input boundary every fragment's
input offset is zero, so their contributions accumulate into the same input
weights; a narrower circuit contributes only to its prefix.

A nonzero `virtual_inputs` count reserves the last entries of the shared input
array as virtual inputs. Each proof defines them as affine functions
`c0 + c1 * x[source]` of committed private inputs (`VirtualInputs`). Both roles
derive the definitions, and they are never absorbed, so they must be fixed
before the participant's sumcheck draws any challenge: derive them only from
data the transcript already binds, never from that proof's own messages. The
prover appends their values to the input array. `compile_packed` substitutes
them like public inputs: each constant moves to the right-hand side and each
linear part joins its source input's weight, so virtual inputs are never
committed. The primary circuit must end before the virtual suffix and so
cannot read it; the other circuits may. `prove` and `reduce` take the
definitions; participants without virtual inputs pass `VirtualInputs::none()`.

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

The statement binds every circuit ID before the commitment (transcript I3).
The public inputs, commitment, sumcheck messages and packing responses precede
the batching boundary on the same transcript, so the handoff to Polygero adds
no query or proof bytes. The rows are never absorbed: both roles derive them
locally, and each `LinearStatement` carries the stamp of the session it was
derived on, which the joint opening checks. `LinearStatement::new` builds a
static system for tests and tools only; nothing absorbs it, and it belongs to
no session, so a complete proof's joint opening rejects it.

`context.rs` derives layouts for both roles. Merkle hashing uses the fixed
Merkle hash domain of v2 commitments, so the statement is the only place
parameters are bound; the evaluation-domain ID is bound nowhere, since the
verifier fixes the domain. The transcript statement absorbs, once and
before any prover message, every circuit (`Circuit`: ID, layer widths and
counts), every participant's `CommitmentLayout`, the `JointGeometry` and the
public inputs (`transcript.rs`, `ZkProofStatement`); after it only prover
messages are absorbed. Circuits are trusted immutable metadata: the runtime
absorbs their IDs without rehashing them. Symbolic pad expressions end at constraint compilation. They are not
serialized, and no intermediate dense input-weight vectors are cached.

## Storage

A participant's value vector is `[private inputs | pads]`. By default every
value is a native cell of its own commitment. `CircuitParticipant::with_storage`
takes a `StorageMap` (`storage.rs`) that marks some values foreign: bits in the
binary commitment. The participant then derives its commitment layout from the
map.

- Mixed storage commits `[native private inputs | pads | R]`, and every pad
  is native. The layer rows read only pads, so they go to this field's
  Polygero participant unchanged. Only the input equation `<w, v> = t` reads
  foreign values. A fresh nonzero `eta` and one masked message
  `mu = eta*<w_F, v_F> + R` split it (`split.rs`) into two parts:
  - a native row `eta*<w_N, v_N> - R + mu - eta*t = 0`, beside the layer
    rows;
  - a modular claim `<eta*w_F, v_F> + R_bits = mu (mod p)` over foreign bit
    groups.
- Pure foreign storage commits nothing. Fresh weights batch every layer row
  and the input equation into one modular claim with a public target
  (`batching.rs`).

The [foreign storage layer](../foreign/README.md) discharges modular claims.
A split participant's `CommitmentLayout` in the statement carries its storage
map as runs and R's bit group.

## Application and encoding

The mdoc application exposes `mdoc::v2::run_mdoc_prover` and
`mdoc::v2::run_mdoc_verifier`, with corresponding deterministic inner entry points.
It connects its hash and signature fields through the
[foreign storage layer](../foreign/README.md), which owns the cross-field
protocol, its round order and its reserved-input layout. The v2
ZK joint wrapper invokes the separate
[witness-selection protocol](../witness_selection/README.md), binding both fields'
masked fingerprints before either sumcheck, and automatically adds the
fingerprint affine equations to the frontend statements.

`packing_commitment.rs` connects the input-packing protocol to committed cells.
This crate builds without the `mdoc` feature.

Proof types and canonical codecs live in `runtime::v2::proto`; the application
envelope is `mdoc::v2::MdocProof`. Standalone ZK proofs use `LFV9` and
include the two masked fingerprint responses. Mdoc
proofs use `MDA7`: an envelope around the generic composed body
(`proto::composed`). The magic is the only one, outermost; the body holds only
prover data in send order, then the terminal rows, nonces and frontier (a u64
digest count, then the digests), so the proof length follows from the geometry
and that count.
Serialization writes backend data directly into the containing proof buffer.
V2 uses tagged messages over SHA-256 strands and a mandatory final seal owned by
the complete-proof encoder; nested circuit and backend bodies have no extra seals.
V1 encodings and transcripts are unchanged.

Tests under `tests/` cover single- and multiple-circuit proofs, binary packing and
prime-field direct inputs, shared input layouts, independent transcript replay,
malformed shapes, altered messages and commitment binding. `src/bin/dependency_check` enforces protocol and role boundaries.
