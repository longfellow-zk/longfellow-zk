# Longfellow V1: soundness and privacy

This library proves knowledge soundness and zero-knowledge simulation
for the modeled v7 protocol. A SHA-256 circuit over GF(2^128) runs first,
followed by an ECDSA circuit over the P-256 base field. Both use Ligero V1
with 132 opened columns and are linked by the v7 MAC.

## Strongest checked results

| Result | Bound and scope | Endpoint |
|---|---|---|
| Knowledge soundness | **125-bit T-security** for all four v7 hash profiles in the annotated ideal-oracle model. Acceptance at the replayed MAC multiplier with failed extraction has probability at most `(N + tA) / 2^125` when `N + tA > 0`, and `33628000 / 2^256` at zero. | [`V7Soundness125.annotated_fs_knowledge_soundness_125`](LfzkV1/V7Soundness125.lean) |
| Zero knowledge with 256-bit nonces | Distinguishing advantage at most `Q / 2^256 + 2^-360` at all four registered v7 Ligero geometries with independent typed Merkle oracles. The simulator receives the common message blocks' zero pattern. | [`V7ZkProfile.v7mac_twofield_zk_deployed_padding`](LfzkV1/V7ZkProfile.lean) |

`N` counts adversarial transcript-oracle queries and `tA` counts adversarial
Merkle-hash queries. They are separate budgets in the experiment.

## Knowledge soundness

For each of the four hash profiles and the registered signature profile,
the checked event satisfies

```text
Pr[both modeled verifiers accept
   and the MAC multiplier annotation equals the decoded key-point answer
   and the extractor returns no witness pair]
  <= (N + tA) / 2^125        if N + tA > 0
  <= 33628000 / 2^256        if N + tA = 0.
```

On the branch where the Merkle trace explains both openings, the adversary
must make at least 13 Merkle queries. This absorbs the fixed replay charge
for positive budgets. At zero queries, only the Merkle exception bound applies.

The experiment fixes the initial application transcript and samples an
independent uniform Merkle tape and ideal prefix-oracle table. The prover
can interleave both kinds of query and select its annotated proof adaptively.
The Merkle tape must supply enough answers for the search and verification.

The extractor gets the submitted proof, its replayed challenges, and the
Merkle queries before the first transcript query naming the final root
pair. On each side it scans the reconstructed tableau for agreement with
the Ligero proximity response. It recovers
each row uniquely on those columns, with radii 14 or 15 for the hash side
and zero for the signature side. It checks both circuit assignments and
compares their common blocks before returning them.
[`extractFromTrace` and `extractFromTrace_valid`](LfzkV1/V7Soundness125.lean)

Lean specifies bounded-distance row recovery by its unique solution on
the supplied positions. For Reed–Solomon rows this is the Berlekamp–Welch
decoding problem. The Lean result checks this specification and its
failure probability. An executable decoder and a running-time theorem
are outside that result.

The proof charges field, Ligero, and MAC failures to the observed query
roles, one replay residual, or a fixed replay allowance. Circuit satisfaction
includes every assert-zero occurrence, including intermediate assertions.
The finite list of possible lifts is an object in the soundness analysis.

## Two-field MAC constraints

The deployed v7 formula for each 128-bit message block is

```text
tag = (av + share) * message.
```

Both circuits receive the same public tag and verifier multiplier, while
their private shares may differ. For fixed witnesses with unequal
messages, equality of the tags has at most one bad multiplier. The
headline's `hrowSatH` and `hrowSatS` hypotheses require every satisfying
circuit assignment to enforce its own MAC equation and the shared tag.

The Rust implementations are
[v1/mac.rs](../../rust/src/mdoc/runtime/v1/mac.rs) and
[v1/verifier.rs](../../rust/src/mdoc/runtime/v1/verifier.rs).
The formal annotation carries the replayed multiplier; it is not an extra
serialized Rust proof field.

## Zero knowledge

The complete V1 view includes both commitments, sumcheck messages,
Ligero responses, authenticated openings, and the shared transcript.
The simulator uses the checked masking/interpolation transformations,
Merkle hiding, and Fiat–Shamir oracle-programming hybrids.

The v7 tag is zero on a zero message block, independently of the private
share. The simulator takes the public inputs and the zero pattern of the
six common 128-bit blocks. The validity of the witness families for all
private shares and adaptive public contexts remains an explicit premise.

In the 256-bit-nonce result, `Q` counts all post-proof observer queries
across the two independent typed Merkle oracles, including repeats and
queries for internal nodes. The observer also receives all five ideal
challenge functions. Honest commitment calls and simulator programming
occur before the observer runs and are outside its budget. The bound
is strictly below `2^-128` through `Q = 2^128 - 1`. At `Q = 2^128` it is
`2^-128 + 2^-360`. If all six common blocks are nonzero, the witness-free
simulator takes only public inputs.
[`v7mac_twofield_zk_nonzero`](LfzkV1/V7ZkProfile.lean)

Rust uses a shared SHA-256 input space for the two trees. The salted
leaf formats have disjoint byte lengths. Both trees use the same 64-byte
encoding for internal nodes, so equal child pairs hash to equal values
across trees in Rust. The theorem's two typed oracles model these as
independent addresses. The deployment correspondence also includes the
concrete field sampler, interpolation domains, and proof encodings.

The joint Merkle hop samples independent leaf labels, computes internal
nodes using the ordinary consistent oracle for each side, and installs
only opened leaf entries. The two raw Ligero challenges on each side can
be sampled first with an exact oracle law. Thus both opening sets are
fixed before salts are revealed, and a single observer query can guess
at most one unopened salt when the column payloads are distinct. A
joint tape bijection then preserves both roots, both openings, both
responses, both sumcheck transmissions and all challenge functions. In
particular the second side uses the preserved first proof for its context.

Each committed column contains all three independent Ligero mask rows.
The low-degree row has degree below `k`. The dot and quadratic rows have
degree below `2k-1`, with zero witness-point sum and zero witness-point
values respectively. For two distinct evaluation points, evaluation
difference is a surjective field-linear map on each mask space. An affine
polynomial suffices for the first row. The product vanishing on the
witness points times a linear polynomial supplies a direction for the
two response masks. Independent masks give a duplicate-payload bound of
`choose(n,2) / |F|^3` per side, conditional on any core padding. The two
terms sum to less than `2^-360` for every profile.

| Circuit | Committed columns `n` | Base cut `k` | Response cut `2k-1` | GF(2^16) witness rows | Salted leaf bytes |
|---|---:|---:|---:|---:|---:|
| Hash, 1 attribute | 3230 | 461 | 921 | 255 | 4288 |
| Hash, 2 attributes | 3318 | 474 | 947 | 258 | 4320 |
| Hash, 3 attributes | 3352 | 478 | 955 | 267 | 4464 |
| Hash, 4 attributes | 3436 | 490 | 979 | 269 | 4496 |
| Signature | 3187 | 455 | 909 | 0 | 640 |

The v7 Ligero prover hashes the 32-byte nonce and each full-width field
element in the committed column, including the dedicated masks. These
leaf lengths also separate the two circuits' leaf preimages from each
other and from 64-byte internal-node inputs. Binary-field sampling uses
16 random bytes per full-field draw. Prime-field sampling rejects
out-of-range values. Interpolation of independent systematic samples
produces uniform rows under the ideal independent byte source. Subtracting
the witness-point sum from the first witness coordinate gives a uniform
dot mask. Clearing the witness coordinates gives a uniform quadratic
mask. The core-padding bijection works over the embedded GF(2^16) on the
selected hash rows.
[Mask sampling and serialization](../../rust/src/runtime/v1/ligero/prover.rs),
[Binary subfield](../../rust/src/runtime/v1/subfield.rs),
[`V7ColumnUniqueness`](LfzkV1/V7ColumnUniqueness.lean).

## Assumptions and deployment boundary

| Boundary | Checked result or retained premise |
|---|---|
| Circuit model | [`ConcreteCircuit`](LfzkV1/ConcreteCircuit.lean), [`ConcreteCircuitBridge`](LfzkV1/ConcreteCircuitBridge.lean), and [`ZkArithProfile`](LfzkV1/ZkArithProfile.lean) construct the circuit semantics and variable-width frontend bridge. `Satisfied` includes outputs and assertions. |
| Registered artifacts | Rust inspectors check circuit IDs, recorded geometries, `WellFormedP`, `Isolated`, and `DeadEnd` on the frozen v7 archives. Identification of those bytes with the supplied Lean circuit remains external. |
| Verifier correspondence | `CircuitSide` retains the public-input maps, `CodeAgreesP`, initial points, message readers, tableau placement, domains, and size bounds. The 125-bit endpoint also requires canonical prefix messages and a signature public input recoverable from its prefix. Linking these maps and the circuit relation to the compiled Rust or C++ verifier remains a premise. |
| Soundness challenge sampling | The ideal prefix oracle returns independent expanded answers with exact role projections. A 256-bit digest can reach at most `2^256` opening sets, while each hash profile has at least `2^396`. Exact initial decoding also assigns positive mass to equal field coordinates, which distinct AES counter blocks exclude. [Checked sampler limits](LfzkV1/V7SamplerAudit125.lean) |
| Commitments and transcript | The mathematical opening check, cut trace, and two-oracle adaptive Merkle reduction are proved. The annotated output fixes the opening sets, the association of opening data to indices, and the MAC multiplier. Rust derives these from replay. The typed annotation and accounting lemmas are standalone steps toward a bridge to the shared SHA-256/AES transcript. |
| MAC rows | Each satisfying assignment must enforce its circuit's tag equation on the intended common value. The supplied-key annotation must agree with the key-point oracle answer in the soundness event. |
| Privacy | The model uses independent typed Merkle and challenge tables, valid witness families, and injective finite encodings. The Ligero decoders are deterministic functions of raw coins. The registered-profile theorem takes the evaluation domains and both frontends as model inputs. For the selected hash witness rows, their small-field membership and the deployed evaluation points' membership in the same embedded subfield give the support premises. |

[`IdealSampler`](LfzkV1/IdealSampler.lean) constructs balanced projections
from a common abstract product alphabet. This establishes an ideal-sampler
construction; it does not identify that alphabet with a single 256-bit
digest or prove correspondence to the deployed expansion.

See the [formal audit](../AUDIT.md) for the shared audit policy and
implementation boundary. The theorems apply to the mathematical models
under the premises stated above.

## Reproduce the checks

From `formal/`:

```sh
lake build
lake build LfzkV1.V7Soundness125
lake build LfzkV1.V7ZkProfile
lake build SecurityAudit
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-profile
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-assertions
```

The declaration audit permits Lean's standard axioms and the documented
native-evaluation facts used by V1 numerical rows and their imported
numerical certificates. The retained Hahn identities themselves use
kernel-checked integer computations. The inspectors compare all five
recorded profiles with the frozen archives and current verifier geometry.
