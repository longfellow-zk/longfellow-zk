# Legacy ZK

`runtime-zk` uses the legacy two-hand `runtime-sumcheck` protocol. `runtime-zk-ng`
uses single-hand sumcheck through a separate crate. Both use the same partition
of responsibilities, with separate implementations and protocol codecs.

Numerical proving advances the main transcript once and returns local verifier
data. Sumcheck's pure symbolic verifier turns that data and the proof into
logical acceptance relations. `constraint_compiler::compile` maps logical pads
to committed witness positions, binds public inputs, and emits sparse Ligero
entries. Zero coefficients are omitted; rows and their constants are retained.
`product_constraints` enforces the committed endpoint-pad products. All sumcheck
algebra, challenge derivation, and pad sampling belong to `runtime-sumcheck`.

Verification independently derives data in sumcheck, constructs the same
relations, and checks their compiled constraints with Ligero. Data and relations
remain local; neither is serialized or accepted from a proof. There is no
transcript fork or symbolic replay during proving. Codecs and geometry stay in
`runtime-proto`, and stored legacy proofs remain compatible.

See [legacy sumcheck](../sumcheck/README.md) for API changes and validation.
