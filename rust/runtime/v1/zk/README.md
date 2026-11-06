# Longfellow v1 ZK

`runtime::v1::zk` combines the legacy two-hand `runtime::v1::sumcheck` protocol
with Ligero commitments. Prover and verifier orchestration have separate modules;
both use the shared constraint compiler and the v1 proof codec.

Numerical proving advances the main transcript once and returns local verifier
data. Sumcheck's pure symbolic verifier turns that data and the proof into
logical constraints. `constraint_compiler::compile` maps logical pads
to committed witness positions, binds public inputs, and emits sparse Ligero
entries. All coefficients are retained, including zeros, along with each row's constant.
`product_constraints` enforces the committed endpoint-pad products. All sumcheck
algebra, challenge derivation, and pad sampling belong to `runtime::v1::sumcheck`.

Verification independently derives data in sumcheck v1, constructs the same
relations, and checks their compiled constraints with Ligero. Data and relations
remain local; neither is serialized or accepted from a proof. There is no
transcript fork or symbolic replay during proving. Codecs and geometry stay in
`runtime::proto`, and stored legacy proofs remain compatible.

See [legacy sumcheck](../sumcheck/README.md) for API changes and validation.

Applications use `mdoc::v1::{ZkSpecStruct, run_mdoc_prover, run_mdoc_verifier}`.
The original spec fields, error codes, and historical proof bytes are preserved.
This system supports circuit versions 5–7 independently of NEXT.

Tests live in `tests/`, including the constraint compiler and deterministic proof
fingerprints. The application's `test_all_circuits_prior_compatibility` verifies
saved proofs and requires freshly generated proofs to match them byte for byte
for every v5, v6, and v7 fixture with one through four attributes.
