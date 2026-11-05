# ZK V2

`runtime::zk_v2` composes projective sumcheck, authenticated input packing and
nonrecursive Polygero. `runtime::zk_v1` retains the separate deployed protocol.
`ZkProver`, `ZkVerifier`, `ZkContext` and `ZkProverCommitment` provide standalone
proofs. `joint::CircuitParticipant` exposes the same reduction for applications
that share one Polygero commitment across fields. Prover and verifier orchestration
stay in separate files; layout and constraint arithmetic are shared.

The [Lean development](../../../formal/lfzk-v2/README.md) proves authenticated
extraction for the layered composition at checkpoint `de904b4`. Its mdoc
model still uses the earlier MAC connection. The current MAC-free adapter
requires a formal extension; complete joint-view zero knowledge also remains
open. Circuit/layout, MAC, binding and ideal-sampler premises for the retained
certificate are documented in the [audit](../../../formal/AUDIT.md).

## Commitment and field participants

`ZkContext` borrows the field and its ordered interpolation domain.
`CircuitParticipant::new` derives immutable proof geometry, witness layout and
Polygero parameters. `prepare` validates and packs typed private inputs, samples
sumcheck pads and returns the witness and owned reduction state. Binary source
inputs are Boolean; prime-field inputs remain field elements.

Each participant binds its packing interpretation and circuit-composition layout
before the shared root. Polygero uses recursive `(Participant, Tail)` tuples ending
in `()`, preserving each field's types. All participants share `(k,s,n,t)`, one
salted tuple-column Merkle tree and one query set. A standalone proof uses the
same backend with one participant. Shared queries do not imply independent
failure events; the per-field residual budgets add.

After commitment, each participant runs its circuit and packing reduction.
`prove` and `verify` return an affine `LinearStatement`. Returning that statement
is not an acceptance decision: the caller must complete the joint Polygero
opening against the root received before sumcheck. All statements are bound
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
layered sumcheck. All must have the same input width and public/private ordering.
`prove_circuits` and `verify_circuits` take that ordered circuit list and the
same public inputs. The prover supplies one private source vector, packed and
committed once. All circuit IDs and the common public values bind before sumcheck.

The input array is shared. Intermediate layers concatenate each active
circuit's wires in list order, without padding between circuits. Sparse
quadratic, linear and constant streams retain local indices; their slices of
the global arrays supply the offsets. At the input boundary every fragment's
input offset is zero, so their contributions accumulate into the same input
weights. There are no independent affine input views or extra advice vectors.

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

Sumcheck algebra belongs to `runtime::sumcheck_v2::symbolic`. Numerical proving
and public reconstruction use the same symbolic builder, returning affine
constraints over logical inputs and pads. Each stage contributes one terminal
constraint, followed by the final input claim. Deriving these constraints alone
does not authenticate them.

`constraint_compiler::compile_packed` substitutes the main public inputs and
maps logical pad positions into committed witness coordinates. It emits sparse
terminal rows and the dense source claim for the packing adapter. The adapter
produces two linear rows for trace-zero packing, or one direct row for degree
one. Degree-one packing introduces no masks, messages or sampling. All equations
use `sum_w A[c,w]*w + b[c] = 0`; coefficients, explicit zeros, duplicate terms
and constants are retained. The fresh sumcheck terminal scale makes the cross
pad and product cell linear in these rows, without backend product-copy checks.

After sumcheck and any packing exchange, each role appends
`longfellow-v2/polygero-statement/v1` and samples a 32-byte statement identifier.
Polygero binds that identifier before its scalar and polynomial challenges.
It adds no proof bytes. The source circuit IDs, public values,
commitment and reduction messages are already bound by the shared transcript;
the identifier makes their handoff explicit. Sparse A/b encoding and term order
are outside this binding. Standalone Polygero callers must bind their own source
statement and ensure their A and b implement it.

`context.rs` derives layouts for both roles. The commitment context contains
only backend dimensions and the ordered field domains, while circuit identities
and packing/composition metadata bind in the surrounding transcript. Circuits
are trusted immutable metadata: the runtime absorbs their IDs without rehashing
them. Symbolic pad expressions end at constraint compilation. They are not
serialized, and no intermediate dense input-weight vectors are cached.

## Application and encoding

The mdoc application exposes `mdoc::v2::run_mdoc_prover` and
`mdoc::v2::run_mdoc_verifier`, with corresponding deterministic inner entry points.
NEXT v10 connects the hash and signature fields through an application-owned
P256 adapter. Its two product trees share the binary input array and layered
sumcheck with the hash circuit. The application commits shared bits only on the
binary side, while native inputs, one hiding scalar and pads stay in the prime
field. It sequences the native reduction, conversion challenges, binary
reduction and packing before one joint opening. V1 retains its frozen versions
5–7 and runtime MACs; the v2 frozen registry is empty.

`native.rs` batches every native sumcheck layer equation and the final input
claim into one linear claim. Its numerical and verifier entry points remain
in separate files. The application adapter uses this staged handoff and the
same packing/constraint primitives as `CircuitParticipant`; the fixed-circuit
API retains its circuit-identity and typed-input checks.

Proof types and canonical codecs live in `runtime::proto`, with the application
envelope under `mdoc::runtime::v2::proto`. Standalone ZK proofs use `LFV7`, mdoc
adapter proofs use `MDA4`, and the shared Polygero envelope uses `JPG1`.
Serialization writes backend data directly into the containing proof buffer.
V1 encodings and transcripts are unchanged.

Tests under `tests/` cover single- and multiple-circuit proofs, binary packing and
prime-field direct inputs, shared input layouts, independent transcript replay,
malformed shapes, altered messages and commitment binding. The global dependency checker enforces protocol and role boundaries.
