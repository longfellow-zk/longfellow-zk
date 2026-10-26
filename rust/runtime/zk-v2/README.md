# ZK V2

`runtime::zk_v2` uses only `runtime::sumcheck_v2`. `runtime::zk_v1` remains the
legacy two-hand entry point. V2 exports `ZkProver`, `ZkVerifier`, `ZkContext`
and the owned `ZkProverCommitment`; its implementation modules are private.
The context borrows the field `f` and ordered interpolation `domain`.
The V2 proof types and codec are in `runtime::proto::zk_v2`.

The [Lean model](../../../formal/lfzk-v2/README.md) proves an authenticated
two-field extraction bound of `(1+N+tA)/2^117` for all query budgets, under
its explicit circuit, MAC, and ideal-sampler premises.
The [audit](../../../formal/AUDIT.md) describes
the correspondence boundary and the remaining joint-view privacy work.

`ZkVerifier::new(circuit, config, context)` prepares and validates public parameters
once. `geometry()` returns the prepared proof shape; commitment reception and
verification reuse those parameters. The verifier owns an immutable circuit.
`receive_commitment()` binds the root before sumcheck. Both proving and verification
borrow public-input slices; proving consumes its commitment state.
Polygero remembers the received root and checks that verification uses that root.
Its methods take the transcript explicitly so sumcheck can run between reception
and verification.
Opened oracle values stay packed by row in the prover, serialized proof, and
verifier, with the selected columns in transcript query order within each row.
The `PLG7` encoding uses dynamic full-field/subfield runs. Only the codec needs the
subfield serializer; verifier geometry and algebra have no row classification.
The prover chooses ordinary-row masks from the circuit's public `subfield_boundary`
and validates all witnesses in that portion before masking. A row crossing the
boundary uses full-field masks; product rows and dedicated masks always do so.
A nonzero `subfield_boundary` requires the entire domain to lie in the subfield.
The committed row order is `u, m`, ordinary witness rows, product triples, then
`fstar`. Batching polynomial indices match all row indices before `fstar`.
The commitment hashes all three rows of each triple. Proofs omit each product
output z; the verifier reconstructs z = x*y before authenticating columns and
checking responses.
H and Z are represented on oracle prefixes starting at K, of lengths K+S and
2K respectively. The verifier interpolates Z back to the logical witness points
and sums those values. T controls both openings and row masks.

Sumcheck protocol algebra belongs to `runtime::sumcheck_v2::symbolic`. Both
sumcheck entry points return constraints over logical inputs and sumcheck pads,
using the same pure symbolic builder internally.

`constraint_compiler::compile` takes those constraints, pad positions from the
protocol codec, and public inputs. It maps logical pads to committed witness
coordinates, substitutes public inputs, and emits sparse Polygero constraints.
All equations keep the zero-sum convention `sum_w A[c,w]*w + b[c] = 0`.
Signed pad coefficients pass through unchanged; the compiler inserts `-1` for
each pad-product slot and subtracts the final weighted circuit inputs.
All terms are retained, including zero coefficients, along with each constraint's
constant.
After the final sumcheck challenge, both roles append the domain tag
`longfellow-v2/polygero-statement/v1` and sample a 32-byte FS statement identifier.
They do this before constraint compilation, then pass the identifier explicitly
to Polygero, which absorbs it before its scalar and polynomial batching challenges.
The identifier is derived locally and adds no proof bytes. Sparse A/b encoding,
term order, duplicate terms and explicit zeros are outside this binding.
The circuit ID, public inputs, commitments and sumcheck messages are already
bound by the shared transcript; the identifier makes their handoff explicit.
Standalone Polygero callers must bind their own source statement and ensure
that their A and b implement it.
`context::product_constraints` fixes the products of the final-claim pads when
preparing the public layout, before either role runs sumcheck.

Proving runs numerical sumcheck directly on the main transcript, receives the proof
and symbolic constraints, compiles the constraints, and continues Polygero.
Verification calls sumcheck v2's `derive_constraints`, compiles the result, and
continues Polygero. Deriving constraints alone does not check them. Constraints
remain local and never appear in the proof codec. There is one final dense
input-weight vector, moved into the input constraint; no intermediate dense
vectors are cached. Sumcheck random values are called pads; mask refers to
Polygero mask rows.

`context.rs` supplies field/domain references and derives the public layout for
both roles: witness counts, pad-product constraints, and proof geometry.
Polygero's commitment context contains only its own parameters, ordered domain
and product layout. Sumcheck absorbs the trusted circuit ID without rehashing
the circuit; the later statement identifier carries that binding into Polygero.
The identifier is sampled by `transcript.rs` and never changes the Merkle context.
The Polygero context tag is `polygero/root/context/fstar-last/v10` and its batching
tag is `polygero/root/challenges/oracle-basis/v6`; frozen v1 transcripts are unchanged.
`prover.rs` owns private-input assembly and
`verifier.rs` handles public reconstruction. Compiler tests live in `tests/`.
Input and proof shapes are validated before advancing the sumcheck transcript.
Symbolic expressions and pad coordinates end after compilation, before Polygero
runs. Consuming the commitment releases its encoded rows and Merkle tree as soon
as the proof is returned. Serialization appends Polygero directly into the
containing proof buffer.

Polygero retains the encoded rows without a second copy of the original witness.
Its `prove` method consumes the commitment state. The verifier checks the linear
constraints; protocol tests also check the arithmetic response independently.

The mdoc application exposes `mdoc::v2::run_mdoc_prover` / `mdoc::v2::run_mdoc_verifier`
and corresponding deterministic inner entry points. Applications explicitly choose this system; its typed specification cannot be
passed to v1. V1 owns versions 5–7 and v2 owns the implemented versions from 8.
`mdoc::v2::MdocProof` and `mdoc::v2::MdocProofGeometry` expose the v2 application proof container.
The frozen v2 registry is empty. NEXT v8 is prepared by the compiler-enabled
application `mdoc::development_provider`, which returns the compiled archive
and its matching spec with concrete Polygero parameters. Runtime providers load
only frozen archives and need no compiler. Circuit generation is independent
of commitment geometry, and the combined-proof marker is `LFV2`.

See [Sumcheck V2](../sumcheck-v2/README.md) for protocol algebra, compiler
selection, shared-suite coverage, and validation commands.

The `experimental` feature also exposes `zk_v2::packed`. Its GF128-specific
`PackedCircuit` owns the circuit/domain contract; `PackedCommitment` owns
the private bits, caller auxiliaries and masks from commitment through proving.
The physical vector is packed words, caller auxiliaries, 127 ring masks,
checksum, then ordinary GKR pads and their products. Its subfield boundary is
zero. Public bits are substituted into the affine right-hand side.

Caller bit-linear equations are bound before GKR and independently combined
after GKR. Ring switching runs next, and only then is the Polygero source
statement identifier sampled. The specialized `PackedZkProof` uses `LFB2`
and adds the 127 masked ring components before Polygero. Direct-field APIs
and LFV2 encoding remain available.

The flat trace adapter needs 128 committed cells and no inner sumcheck or
tower construction. Its entire response precedes the independent batching
challenges, and it emits one native backend equation.

This path is a Rust prototype; its security composition is outside the v8
Lean theorem. See [ring switching](../ring-switch/README.md) for its algebra,
ownership contract and deferred proof obligations.
