# ZK NG

`runtime-zk-ng` uses only `runtime-sumcheck-ng`. `runtime-zk` remains the
legacy two-hand entry point, with the same separation of symbolic verification
and constraint compilation. Both export `ZkProver`,
`ZkVerifier`, and `common::ZkContext`; select the crate at the import boundary.
The NG proof types and codec are in `runtime-proto::zk_ng`.

Sumcheck protocol algebra belongs to `runtime-sumcheck-ng::symbolic`. Its pure
symbolic verifier takes proof messages and local `VerifierData` and returns
acceptance relations over logical inputs and sumcheck pads.

`constraint_compiler::compile` takes those relations, pad positions from the
protocol codec, and public inputs. It maps logical pads to committed witness
coordinates, substitutes public inputs, and emits sparse Ligero constraints.
`product_constraints` supplies the quadratic constraints for committed
endpoint-pad products, including during commitment. Zero coefficients are
omitted; constraint rows and their constants are retained.

Proving runs numerical sumcheck directly on the main transcript, builds symbolic
relations from its verifier data, compiles them, and continues Ligero.
Verification independently derives data with sumcheck-ng's
`derive_verifier_data`, builds and compiles the same relations, and continues
Ligero. Data derivation alone does not check the sumcheck equations. The data and
relations remain local and never appear in the proof codec. There is one final
dense input-weight vector, moved into the input relation; no intermediate dense
vectors are cached. Sumcheck random values are called pads; mask refers to Ligero
mask rows.

`common.rs` supplies context and the statement hash. `prover.rs` and `verifier.rs`
drive the flows. There is no observer, transcript replay, strategy selector, or
dependency on the legacy sumcheck/ZK crates. Commitment and Ligero primitives
remain shared.

The mdoc application exposes `run_mdoc_prover_ng` / `run_mdoc_verifier_ng`
and corresponding deterministic inner entry points. The existing version-aware
application wrappers dispatch mdoc v8 to these NG functions and v5-v7 to legacy.
`MdocProofNg` and `MdocProofGeometryNg` expose the distinct NG application proof
container. Fresh mdoc compilation and MLDSA proof tests use NG geometry.

See [Sumcheck NG](../sumcheck-ng/README.md) for the source comparison against
main, intentional legacy test fixture changes, protocol algebra, and validation
commands.
