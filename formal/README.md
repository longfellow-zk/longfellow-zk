# Formal verification

The current MAC-free mdoc composition has a Fiat--Shamir extractor theorem for
the mathematical runtime verifier with adaptive public requests:
[`MdocSharedSHASoundness.ratio_le`](lfzk-v2/LfzkV2/Current/MdocSharedSHASoundness.lean) proves
for all integers `Q >= 0` and `Q_H >= 0`, any finite classical adaptive
adversary making at most `Q` distinct transcript-oracle queries and at most
`Q_H` SHA-256-oracle calls satisfies

```text
Pr[verifier accepts and the paired extractor fails to recover
   a witness satisfying the requested circuits]
  <= 2Q / 2^128
     + [4Q + 1 + Q_H(Q_H - 1)/2
        + (4886 + Q_H)(2Q_H + R + Q + 2)] / 2^256.
```

`R` counts ordinary round boundaries, excluding the final seal: 492 for two
attributes and 499 for four. Repeated inputs receive the same complete answer;
arbitrary finite repetitions and `Q = 0` are included. Probability is over the
ideal oracles and the adversary's private randomness.
Its checked rate-1/7 profile is `(k,s,n,t)=(349,12,2443,84)`.
It includes early witness selection,
both fields, the cross-field adapter, packing, joint Polygero, one Merkle tree
and the final seal. The [current model](lfzk-v2/README.md#current-mac-free-protocol)
states its circuit/layout and ideal-sampler premises. Acceptance and the
application/backend failure cover are derived from the modeled verifier;
there is no supplied `Execution` or correspondence certificate. Canonical
query bytes, the actual Merkle encoding, requested-public readback and the
first-context extractor are connected in the theorem. The current mdoc
specialization constructs the advice decoder, backend coordinates, transcript
metadata and circuit plans from canonical scalar representations and trusted
sparse circuit descriptions. Oracle answers use the explicit ideal-sampler
model. A reduction from full SHAKE byte streams and machine verification of Rust
are outside this result.
One SHA function supplies setup and generated-circuit identifiers, the
adversary's raw SHA answers and Merkle verification. Its Merkle restriction
uses a uniform lazy tape; every independent finite auxiliary SHA marginal
is averaged without an extra error term. `Q_H` conservatively bounds all
SHA calls in the original adversarial program, including auxiliary inputs.
`runtime::v2::zk` owns the selected joint boundary; mdoc supplies its frontend reductions.
Packing is internal to ZK and binds its statement bytes, profile and cell
counts. Its source coefficients and affine RHS are reconstructed from the
preceding bound messages and oracle answers, without absorbing them again.
The local source is independent of the current packing answer, and the
accepted-path replay recovers the same frontend claim. No new statement-binding
certificate or oracle assumption is introduced by this omission.

The complete mdoc model also has a statistical zero-knowledge theorem:
[`MdocZeroKnowledge.statClose`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocZeroKnowledge.lean).
One witness-free simulator produces the complete proof and the observer's
view, including arbitrary retained private state and both raw oracle traces.
At rate 1/7 its distinguishing error is at most
`(95462672+4886*Mpre+4718*Mpost)/2^256 + 4884*Mpre/2^512 + Tpre/2^46208`.
The [precise scope](lfzk-v2/README.md#complete-mdoc-zero-knowledge) states the
fixed-witness, trusted-circuit and ideal-oracle assumptions. This theorem
combines the frontend, adapter, packing, joint backend and Merkle simulation;
it is separate from extraction soundness.

## Assumptions and remaining correspondence obligations

These are the premises and limits of the current mathematical results. A
successful kernel check establishes the stated implications; it does not
establish that a cryptographic implementation satisfies their premises.

- **Classical ideal oracles.** SHA-256 is a 256-bit random oracle. The
  transcript uses an independent ideal whole-answer oracle: one answer
  contains the 32-byte link and the entire jointly distributed challenge
  block, and repeated inputs return the same answer. Sampling is uniform,
  including rejection sampling, nonzero scalars and openings without
  replacement. This is a joint oracle assumption, stronger than uniform
  marginal field samples. The proofs do not couple the observer's complete
  raw SHAKE output, rejected bytes or unused XOF tails to that answer. There
  is no quantum-oracle result or proof of SHA-256/SHAKE256 security.
- **Fresh private randomness.** Prover masks, pads, commitment nonces and
  the other private coins are independent and uniform. The normal Rust mdoc
  entry point obtains randomness from the operating system. APIs accepting
  a caller-supplied generator require the same randomness property. Merkle
  nonces have 256 bits; they are not assumed collision-free.
- **Fields and representations.** The modeled fields satisfy their field
  laws; bases and scalar representations have their declared cardinality,
  canonical encoding and injectivity properties. The ZK specialization
  explicitly requires binary basis coordinate zero equal to one and a
  successful primitive-generator check.
  Rust limb arithmetic, finite-machine operations and compiler correctness
  are source-correspondence obligations, not additional Lean theorems.
- **Trusted application circuits and archives.** Extraction returns a
  witness satisfying the supplied circuits, not an independently formalized
  ISO mdoc/CBOR specification. Privacy additionally requires signature
  satisfaction and `MdocWitness.HashValid`: ordinary hash assertions must
  remain valid for every reserved mask/OTP suffix and every generated-adapter
  parameter. This noninterference premise is stronger than one satisfying
  assignment. Rust's normal `for_spec` loader checks archive metadata but
  does not recompute semantic payload IDs. Consequently, trust includes
  the actual supplied archive bytes, not merely their advertised IDs.
- **Public setup and resource bounds.** Trusted sparse topology, canonical
  scalar codecs, capacity/address/serialization bounds and the concrete
  hash-depth restriction are explicit. Current parameter certificates,
  sampler projections, advice decoding, generated adapter equations,
  authenticated row layouts and failure coverage are constructed and
  proved; no caller-supplied execution or soundness certificate replaces
  those proofs.
- **Adversary and witness scope.** The adversary is classical and makes
  finitely many calls within the stated budgets; extraction counts distinct
  transcript inputs. Privacy permits arbitrary retained private context
  and adaptive public requests, but uses a fixed witness map per request,
  independent of oracle answers. Validity is required only at requests
  reachable in actual consistent executions. This does not prove privacy
  for arbitrary adaptive selection of a new witness after oracle answers.
- **Efficiency and implementation.** Extraction uses mathematical finite
  search; no polynomial-time extractor bound is proved. The explicit public
  simulator has no witness argument, but its running time is not formally
  bounded. Rust correspondence is reviewed and tested, rather than a
  mechanized refinement. A complete Rust-to-Lean verifier replay vector and
  a separate end-to-end honest-acceptance theorem remain absent. No timing,
  memory-observation or other implementation side-channel theorem is claimed.

**Shared SHA composition.** The original
[`MdocProofRate7.ratio_le`](lfzk-v2/LfzkV2/Current/MdocProofRate7.lean)
is the conditioned endpoint with a fixed auxiliary identifier-hash function.
The shared-SHA theorem above derives the public setup from the actual SHA
function, preserves the serialized proof and verifier decision, and identifies
the exact first-context extractor trace with the Merkle-domain projection of
the original execution prefix. Its transcript-query premise refers only to
the original program with its actual SHA-derived public values. Domain
separation and averaging preserve the bound; no observed-trace independence
or oracle-correspondence certificate is a premise. The intermediate identities
are checked in
[`MdocSHAExperiment`](lfzk-v2/LfzkV2/Current/MdocSHAExperiment.lean).

The common finite-table split, inclusion and extension maps live in
[`SHAProbability`](lfzk-v2/LfzkV2/Current/SHAProbability.lean). Soundness and
statistical privacy reuse those maps; soundness does not import the privacy
composition proofs. The canonical verifier is constructed once, and its
auxiliary-domain invariance holds for every decoded proof. The generic lazy
execution identities need no default transcript challenge, including when
the transcript-query alphabet is empty.

The application-circuit audit found namespace/CBOR-path binding and selected-field
range issues. Rust now rejects reads into SHA padding, incomplete docType matches,
inconsistent wrapper lengths and wrong attribute CBOR types. A bounded CBOR parser,
namespace/path binding and timestamp semantics remain deferred. The protocol proof
continues to trust the supplied application relation; extraction alone does not
establish the intended document semantics.

Canonical query capacities are structural bounds on public vector counts,
fixed codec widths and framing overhead. They do not enumerate field-valued
packets or append padding. Generic codec-length, sampler-projection and runtime
wrapper lemmas keep these representation details separate from the soundness
and privacy arguments. Evaluation and interpolation are linked by a proved
bijection with an explicit equality to Lagrange interpolation. Abstract history
transitions, partial frontend bodies and public-request invariance lemmas let
backend proofs reuse their checked interfaces without unfolding full frontend
executions. These interfaces preserve the verifier, probability bounds and
assumptions stated above.

The broad axiom audit checks new public and private declarations against
`propext`, `Classical.choice` and `Quot.sound`. These foundational axioms do
not discharge any implementation or oracle premise above. Retained V1
certificates keep their separately documented native-evaluation allowance.

## Retained results and component libraries

**The retained layered-sumcheck Longfellow V2 checkpoint has a 116-bit
work-normalized extraction bound.** Sparse quad fragments share one wire
array per layer and one input array. Circuits may have different depths,
scalar outputs, or no layers. Binary packing, linear-only Polygero and the
retained two-field MAC compose with one authenticated tuple tree and one
shared set of column queries.
[`LfzkV2.Layered.Joint.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Layered/Joint/RawRuntimeExtraction.lean)
proves `Pr[accept and paired extraction fails] <= (1+N+tA)/2^116` for all
transcript-query budgets `N` and Merkle-query budgets `tA`. The
[V2 README](lfzk-v2/README.md) identifies the immutable source snapshot and
exact finite bound. Circuit/layout, ideal sampler, MAC-row and codec
premises remain explicit; see the [implementation boundary](AUDIT.md).
The earlier `Joint` (`8943498`), `Linear` (`21cb029`), `Native`, `Packed`,
and V1 proof modules remain unchanged.

The current code also has a separate [witness-selection component](witness-selection/README.md).
Its finite-field IOP analysis charges `choose(L,2)/q²` for two masked
fingerprints. Its adaptive total-oracle component charges `Q*choose(L,2)/q²`;
ordinary fixed-witness quadratic sumcheck charges `2Q/q`. The new
[chained-transcript library](transcript-v2/README.md) proves the required
query-order and charging lemmas with a common exception `(Q+1)/2^256` for
32-byte links, under its typed full-parent preimage and local reduction laws.
The Polygero adapter removes the frontend candidate-list multiplier while
retaining backend extraction/outside-list errors. Rust encoding/sampler
correspondence remains an explicit implementation boundary. The current
composition uses these results without altering the retained certificates above.

The separate [`LfzkV2.Current` model](lfzk-v2/README.md#current-mac-free-protocol)
specifies the current MAC-free mdoc query schedule, typed messages and challenge
blocks, shared opening set and body-binding final seal. It proves structural
prefix/parent laws and counts all runtime boundary queries, including empty
sample blocks and the final seal. Source identifiers are bound without a
separate query. Its end-to-end theorem derives failure coverage and shared-query
charging for typed runtime acceptance, with verifier replay appearing only
in the digest-sized Merkle term.
The schedule tests and foundational-axiom checks are default build targets.

The prior product-checked snapshot `fcf8a3a` retains its separate
[`Packed.RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/Packed/RawRuntimeExtraction.lean)
certificate without changes. Its constants do not describe the randomized
linear terminal.

The earlier v7 verifier using Ligero V1 retains its 116-bit extraction and
false-statement soundness bounds for signature and SHA circuits with one
through four attributes. Its flat zero-query and graded positive-query
proofs are checked by [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean).
The [Longfellow V1 README](lfzk-v1/README.md) states their premises.

Version 7 uses Ligero V1; version 8 uses Polygero. The
[Ligero README](ligero/README.md) documents the component analysis.

The default `lake build` includes all 16 retained Hahn/Delsarte certificate
families: five runtime Polygero profiles, six v7 Ligero mask certificates, and
five Polygero benchmark certificates. It also checks their numerical endpoints
and an [axiom audit](parameters/hahn/RuntimeHahn/APITest.lean). The Hahn identities
use exact integer checks and a proved polynomial interpolation theorem; no
native-evaluation axiom is needed for the certificates.

Run `lake build` or `scripts/build.sh` from this directory to build the default
targets with Lean and Lake's default concurrency. The script also accepts individual Lake targets.

The Ligero development proves:

- Reed–Solomon code distance, affine triple-counting and selected-MCA bounds,
  and JB agreement with checked η³ threshold parameters.
- Delsarte's LP bound using Hahn kernels for uniform intersection families,
  with Johnson as the degree-one case. It certifies the V1 unchecked-mask list
  below the Johnson threshold.
- Response-assisted scalar IOP extraction for Ligero V1, together
  with response-uniform envelopes and false-statement soundness.
- Merkle prefix binding and typed Fiat–Shamir query bookkeeping.
- Exact IOP certificates for v7 signature and hash geometries, and local
  challenge/query count certificates for the hash
  geometries and V1 signatures.

See the [Ligero README](ligero/README.md) for component theorem names and
certificates. This package also contains the EC/ECDSA circuit development and
two sumcheck libraries:

- [Sumcheck V1](sumcheck-v1/SumcheckV1/README.md), imported as `SumcheckV1`,
  contains the legacy round, chain, and challenge-tape proofs used by `LfzkV1`.
- [Sumcheck V2](sumcheck-v2/README.md), imported as `SumcheckV2`, proves the
  projective round update, honest table folding, single-hand layer reduction,
  masked constraint equations, and challenge-tape bounds. These are component
  theorems; the `LfzkV1` security certificates above still use V1.

The retained [Longfellow V2](lfzk-v2/README.md) checkpoints, imported as
`LfzkV2`, connect the native affine circuit, linear and quadratic assertions,
honest prover, and actual
compiled rows. Its staged replay fixes the packing response `U` before an
independent vector challenge and the scalar response `A` afterward. Packing
and layer checks read the same authenticated cells. The degree-one signature
path keeps its original source equation and has no packing challenge or cost.

In the retained layered checkpoint, the packed hash and direct signature sides use geometry
`(n,k,s,t) = (2912,416,15,86)`, with certified candidate bounds 25 and 33.
Before Merkle costs, the adaptive bound is
`1384*N/2^128 + 19303/2^128 + 21661/2^255`; raw verification adds one transcript
lookup. The coefficient includes both correlated shared-query residuals;
the single tree contributes one Merkle explanation error. Both frontends and
packing statements precede either backend challenge, and both responses
precede the shared query. The authenticated extractor returns satisfying witnesses with equal
common messages. Exact startup and small-Merkle bounds yield the all-budget
116-bit endpoint above. This conservative numerical certificate includes
`2/(|F|-1)` per layer, with 20 hash layers and 21 signature layers; the
field-normalized theorem retains the exact nonzero denominator. The older
product-checked and unpacked compositions remain separate models.

The retained checkpoints' backend response/opening simulation and affine-MAC
privacy remain component results. The complete privacy theorem above concerns
the current MAC-free mdoc model.
API and axiom checks are in the default build. Rust arithmetic, concrete
layouts, parsing and byte-level transcript correspondence remain implementation
obligations.

The [recursive Polygero development](polygero/README.md) proves witness
extraction for the transmitted recursive public-coin verifier, with failure
bound `1 − ∏ᵢ(1 − εᵢ)` from certified local errors. False-statement soundness
is derived from extraction validity and the same failure bound. It reuses
the Ligero code and tableau infrastructure.

[Dual packing](dual-packing/README.md), imported as `DualPacking`, proves
trace-pairing coordinate recovery and the two native linear constraints for
packing over arbitrary finite field extensions. Its fixed-commitment
false-claim bound is `1 / |F|`, including arbitrary committed mask cells.
The library and its binary and odd-characteristic regression cases are in
the default build. The retained compiler and staged Fiat–Shamir composition in
`LfzkV2.Linear.Runtime` and the joint transcript lift this fixed-claim bound to the authenticated endpoint above.

From this directory:

```sh
lake build
```

The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.
