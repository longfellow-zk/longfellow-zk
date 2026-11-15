
Every input of `reduce_and_authenticate` and where the transcript absorbs
it (transcript I1 to I4):

- `session`: the composed statement it opened with, absorbed first: the
  application's identity message; a `Circuit` message per circuit (host
  circuit, adapter fragment, split circuit), whose ID hashes the whole
  circuit; both fields' `CommitmentLayout` (packing, cell counts, the split
  participant's storage runs and R's bits); the mode's `AdapterLayout`
  (mode ID, Q, tree shape, pads); `JointGeometry` (the profile); both
  fields' `PublicInputs`. The parsing geometry, the input layouts and the
  mode's claim widths are derived from these.
- `proof`: the body, parsed against the geometry the statement wrote; each
  interactive field is absorbed as its prover message where it is sent.
  The application's complete reader checks the seal over every byte.

The evaluation domains are the composition's own; the transcript does not
absorb them, and each participant rejects a domain other than the one it
was built with. There is no argument for a geometry, a circuit or public
inputs.

It is not complete verification, so it is crate-private: only an
application's complete verifier (`run_mdoc_verifier`), which checks the
seal, calls it. Outside the crate it cannot be called:

```compile_fail,E0624
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
    v2::{
        foreign::{adapter::p256::P256Mode, compose::ComposedStatement, word::MaskedWord},
        proto::composed::ComposedProof,
        transcript::{Opened, ZkStatement},
    },
};
type Statement<'s, DH, DS> = ComposedStatement<'s, 4, P256Field, DH, DS, P256Mode<9>, ZkStatement<'s>>;
type Proof = ComposedProof<2, Gf2_128Field, 4, P256Field, [MaskedWord<9>; 2]>;
fn verify<'s, DH: EvaluationDomain<2, Gf2_128Field>, DS: EvaluationDomain<4, P256Field>>(
    session: Opened<'_, Statement<'s, DH, DS>>,
    proof: &Proof,
) {
    let _ = ComposedStatement::reduce_and_authenticate(session, proof);
}
```

nor under its former public name:

```compile_fail,E0599
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
    v2::{
        foreign::{adapter::p256::P256Mode, compose::ComposedStatement, word::MaskedWord},
        proto::composed::ComposedProof,
        transcript::{Opened, ZkStatement},
    },
};
type Statement<'s, DH, DS> = ComposedStatement<'s, 4, P256Field, DH, DS, P256Mode<9>, ZkStatement<'s>>;
type Proof = ComposedProof<2, Gf2_128Field, 4, P256Field, [MaskedWord<9>; 2]>;
fn verify<'s, DH: EvaluationDomain<2, Gf2_128Field>, DS: EvaluationDomain<4, P256Field>>(
    session: Opened<'_, Statement<'s, DH, DS>>,
    proof: &Proof,
) {
    let _ = Statement::<'s, DH, DS>::verify(session, proof);
}
```

Positive control: the types the calls above name are public.

```
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
    v2::{
        foreign::{adapter::p256::P256Mode, compose::ComposedStatement, word::MaskedWord},
        proto::composed::ComposedProof,
        transcript::{Opened, ZkStatement},
    },
};
type Statement<'s, DH, DS> = ComposedStatement<'s, 4, P256Field, DH, DS, P256Mode<9>, ZkStatement<'s>>;
type Proof = ComposedProof<2, Gf2_128Field, 4, P256Field, [MaskedWord<9>; 2]>;
fn hold<'s, DH: EvaluationDomain<2, Gf2_128Field>, DS: EvaluationDomain<4, P256Field>>(
    session: Opened<'_, Statement<'s, DH, DS>>,
    proof: &Proof,
) {
    let _ = (session, proof);
}
```
