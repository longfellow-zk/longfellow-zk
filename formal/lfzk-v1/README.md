# Longfellow V1: soundness and privacy

This library proves conditional extraction, soundness, and zero knowledge
for the modeled v7 protocol. A SHA-256 circuit over GF(2^128) runs first,
followed by an ECDSA circuit over the P-256 base field. Both use Ligero V1
with 132 opened columns and are linked by the v7 MAC.

## Strongest checked results

| Result | Bound and scope | Endpoint |
|---|---|---|
| Combined extraction and false-statement soundness | **116-bit T-security:** `(1+N+tA)/2^116`, for all query budgets and all four v7 hash profiles. Each circuit has its own private MAC witness. | [`LfzkV1.FlatV7All`](LfzkV1/FlatV7All.lean) |
| Zero knowledge with 256-bit nonces | Two-field statistical distance at most `2^-127` against distinguishers making at most `2^115` Merkle queries. The simulator receives the common message blocks' zero pattern. | [`CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115`](LfzkV1/CompiledLongfellowZkV7Mac.lean) |
| Statistical zero knowledge with 542-bit nonces | Two-field statistical distance at most `2^-131`, with no distinguisher query bound. The simulator receives the same zero pattern. This configuration uses longer nonces. | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542` |
| Witness indistinguishability with 256-bit nonces | At most `2^-127` per side and `2^-126` for two fields at `2^115` Merkle queries; the two-field v7 claim requires equal zero patterns. | [`CompiledLongfellowZk.compiled_longfellow_wi`](LfzkV1/CompiledLongfellowZk.lean), `CompiledLongfellowZkV7Mac.twofield_wi_v7` |

`N` counts adversarial transcript-oracle queries and `tA` counts adversarial
Merkle-hash queries. Writing `T = N+tA`, 116-bit T-security means success
probability at most `(1+T)/2^116`, rather than a fixed probability
`2^-116` for every attacker.

## End-to-end soundness

For each v7 hash/signature pair with one through four attributes, the
checked extraction event satisfies

```text
Pr[both modeled verifiers accept
   and the MAC-key annotation equals the oracle answer at the two roots
   and no extracted pair satisfies both circuits with equal common messages]
  <= (1 + N + tA) / 2^116.
```

The false-statement corollary bounds acceptance when no satisfying pair
with equal common messages exists. The probability is over one uniform
Merkle tape and one uniform transcript oracle. The prover can interleave
both kinds of query, change commitments, grind, and adaptively select its
proof. The tape-size premise supplies enough answers for that execution;
it does not impose an additional adversarial query limit.

The four endpoint modules are:

| Hash attributes | Module | Extraction and soundness endpoints |
|---|---|---|
| 1 | [`FlatV7Headline`](LfzkV1/FlatV7Headline.lean) | `v7Hash1_deployed_fs_extraction_116_circuit`, `v7Hash1_deployed_fs_false_statement_116` |
| 2 | [`FlatV7Hash2Headline`](LfzkV1/FlatV7Hash2Headline.lean) | `v7Hash2_deployed_fs_extraction_116_circuit`, `v7Hash2_deployed_fs_false_statement_116` |
| 3 | [`FlatV7Hash3Headline`](LfzkV1/FlatV7Hash3Headline.lean) | `v7Hash3_deployed_fs_extraction_116_circuit`, `v7Hash3_deployed_fs_false_statement_116` |
| 4 | [`FlatV7Hash4Headline`](LfzkV1/FlatV7Hash4Headline.lean) | `v7Hash4_deployed_fs_extraction_116_circuit`, `v7Hash4_deployed_fs_false_statement_116` |

Names are under `LfzkV1.CompiledZk`. The shared
[`FlatV7All`](LfzkV1/FlatV7All.lean) target imports and audits all eight
endpoints in the default build.

The proof combines flat extraction at zero transcript queries with a
graded extraction-first compiler for positive query counts. Both branches
bound the same enlarged-radius extraction event. Circuit satisfaction
includes every assert-zero occurrence, so a failed intermediate assertion
is covered even when all final outputs are zero.

The main chain runs from the trusted quadratic circuit and its structural
premises through the padded sumcheck/assertion replay, Ligero decoder,
shared-query Fiat–Shamir compiler, two-field MAC, and Merkle extraction
reduction to the exact numerical comparison. The extractor searches finite
lists associated with the committed oracles. An efficient Rust witness
recovery algorithm is not part of this theorem.

## Two-field MAC constraints

The deployed v7 formula for each 128-bit message block is

```text
tag = (av + share) * message.
```

Both circuits receive the same public tag and verifier multiplier, while
their private shares may differ. For fixed witnesses with unequal
messages, equality of the tags has at most one bad multiplier. The
headline's `hrowSat₁` and `hrowSat₂` hypotheses require every satisfying
circuit assignment to enforce its own MAC equation and the shared tag.

The Rust implementations are
[v1/mac.rs](../../rust/applications/mdoc_zk/runtime/src/v1/mac.rs) and
[v1/verifier.rs](../../rust/applications/mdoc_zk/runtime/src/v1/verifier.rs).
The formal annotation carries the replayed multiplier; it is not an extra
serialized Rust proof field.

## Zero knowledge

The complete V1 view includes both commitments, sumcheck messages,
Ligero responses, authenticated openings, and the shared transcript.
The simulator uses the checked masking/interpolation transformations,
Merkle hiding, and Fiat–Shamir oracle-programming hybrids.

The v7 tag is zero on a zero message block, independently of the private
share. Its privacy theorem therefore gives the simulator the zero pattern
of the six common 128-bit blocks. The corresponding witness
indistinguishability statement compares messages with equal zero patterns.
The validity of the witness families for all private shares and adaptive
public contexts remains an explicit premise.

The 256-bit-nonce theorem uses a query-bounded distinguisher. The
542-bit-nonce theorem instead controls statistical distance even when
the distinguisher receives the whole Merkle oracle. These are separate
configurations with the bounds in the result table.

## Assumptions and deployment boundary

| Boundary | Checked result or retained premise |
|---|---|
| Circuit model | [`ConcreteCircuit`](LfzkV1/ConcreteCircuit.lean), [`ConcreteCircuitBridge`](LfzkV1/ConcreteCircuitBridge.lean), and [`ZkArithProfile`](LfzkV1/ZkArithProfile.lean) construct the circuit semantics and variable-width frontend bridge. `Satisfied` includes outputs and assertions. |
| Registered artifacts | Rust inspectors check circuit IDs, recorded geometries, `WellFormedP`, `Isolated`, and `DeadEnd` on the frozen v7 archives. Identification of those bytes with the supplied Lean circuit remains external. |
| Verifier correspondence | `CircuitSide` retains the public-input maps, `CodeAgreesP`, initial points, message readers, tableau placement, domains, and size bounds. Source-level equivalence to the Rust or C++ verifier is not proved. |
| Challenge sampling | Independent uniform ideal transcript answers and exact balance for every decoder role, including joint initial tuples, field pairs, Ligero challenges, fixed-size query sets, and the MAC multiplier. The numerical headline retains its declared answer-alphabet and field-cardinality hypotheses. |
| Commitments and transcript | The mathematical opening check, cut trace, and adaptive Merkle reduction are proved. Byte encodings, field arithmetic, SHA/AES expansion, rejection sampling, and byte-level transcript correspondence remain implementation obligations. |
| MAC rows | Each satisfying assignment must enforce its circuit's tag equation on the intended common value. The supplied-key annotation must agree with the key-point oracle answer in the soundness event. |
| Privacy | Injective encodings, valid witness families, the stated nonce configuration, and the v7 zero-pattern leakage. |

The 116-bit endpoints explicitly assume `|C| = |D| = 2^256` and
`|Fmac| = 2^128`, in addition to the circuit sides' field and decoder
premises.

[`IdealSampler`](LfzkV1/IdealSampler.lean) constructs balanced projections
from a common abstract product alphabet. This establishes an ideal-sampler
construction; it does not identify that alphabet with a single 256-bit
digest or prove correspondence to the deployed expansion.

See the [formal audit](../AUDIT.md) for the shared audit policy and
implementation boundary. These are conditional mathematical security
theorems, not source-level verification of the implementation.

## Reproduce the checks

From `formal/`:

```sh
lake build
lake build LfzkV1.FlatV7All
lake build SecurityAudit
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-profile
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-assertions
```

The declaration audit permits Lean's standard axioms and the documented
native-evaluation facts used by V1 numerical rows and their imported
numerical certificates. The retained Hahn identities themselves use
kernel-checked integer computations. The inspectors compare all five
recorded profiles with the frozen archives and current verifier geometry.
