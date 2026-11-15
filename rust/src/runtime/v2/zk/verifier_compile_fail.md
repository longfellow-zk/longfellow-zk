
Every input of `ZkVerifier::verify` and where the transcript absorbs it
(transcript I1 to I4):

- `self`: the circuit, through its ID in the `Circuit` message (the ID
  hashes the whole circuit); the participant, in `CommitmentLayout`; the
  geometry's profile, in `JointGeometry`; the rest of the geometry is
  derived from those. `verify` rejects a session opened with another
  verifier's statement.
- `session`: the statement it opened with, absorbed first: `ZkStatement`
  (protocol ID, context), the `Circuit`, `CommitmentLayout` and
  `JointGeometry` messages above, and the public inputs in `PublicInputs`.
- `proof`: parsed against the geometry the session's statement wrote; each
  interactive field is absorbed as its prover message where it is sent,
  and the seal covers every byte before the seal block.
- `ctx`: the field, whose FieldID is in `CommitmentLayout` and in every
  Elements value, and the evaluation domain, which the verifier fixes and
  the transcript does not absorb; the participant rejects a domain other
  than the one it was built with.

The verifier takes no geometry, circuit or public inputs except through the
statement and the session. The call that verifies:

```
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::zk::ZkProof,
        transcript::{Opened, Unverified, VerifiedProof},
        zk::{ZkContext, ZkProofStatement, ZkVerificationError, ZkVerifier},
    },
};
fn verify<D: EvaluationDomain<2, Gf2_128Field>>(
    v: &ZkVerifier<2, Gf2_128Field>,
    session: Opened<'_, ZkProofStatement<'_, 2, Gf2_128Field>>,
    proof: Unverified<'_, ZkProof<2, Gf2_128Field>>,
    ctx: &ZkContext<'_, 2, Gf2_128Field, D>,
) -> Result<VerifiedProof, ZkVerificationError> {
    v.verify(session, proof, ctx)
}
```

There is no argument for a geometry,

```compile_fail,E0061
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::zk::{ZkProof, ZkProofGeometry},
        transcript::{Opened, Unverified},
        zk::{ZkContext, ZkProofStatement, ZkVerifier},
    },
};
fn verify<D: EvaluationDomain<2, Gf2_128Field>>(
    v: &ZkVerifier<2, Gf2_128Field>,
    session: Opened<'_, ZkProofStatement<'_, 2, Gf2_128Field>>,
    proof: Unverified<'_, ZkProof<2, Gf2_128Field>>,
    ctx: &ZkContext<'_, 2, Gf2_128Field, D>,
    geometry: &ZkProofGeometry,
) {
    let _ = v.verify(session, proof, ctx, geometry);
}
```

a circuit,

```compile_fail,E0061
use longfellow_zk::{
    core::proto::v2::Circuit,
    runtime::{
        algebra::{gf2_128::Gf2_128Field, range_interpolation::EvaluationDomain},
        v2::{
            proto::zk::ZkProof,
            transcript::{Opened, Unverified},
            zk::{ZkContext, ZkProofStatement, ZkVerifier},
        },
    },
};
fn verify<D: EvaluationDomain<2, Gf2_128Field>>(
    v: &ZkVerifier<2, Gf2_128Field>,
    session: Opened<'_, ZkProofStatement<'_, 2, Gf2_128Field>>,
    proof: Unverified<'_, ZkProof<2, Gf2_128Field>>,
    ctx: &ZkContext<'_, 2, Gf2_128Field, D>,
    circuit: &Circuit<Gf2_128Field>,
) {
    let _ = v.verify(session, proof, ctx, circuit);
}
```

or public inputs,

```compile_fail,E0061
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::zk::ZkProof,
        transcript::{Opened, Unverified},
        zk::{ZkContext, ZkProofStatement, ZkVerifier},
    },
};
fn verify<D: EvaluationDomain<2, Gf2_128Field>>(
    v: &ZkVerifier<2, Gf2_128Field>,
    session: Opened<'_, ZkProofStatement<'_, 2, Gf2_128Field>>,
    proof: Unverified<'_, ZkProof<2, Gf2_128Field>>,
    ctx: &ZkContext<'_, 2, Gf2_128Field, D>,
    public: &[bool],
) {
    let _ = v.verify(session, proof, ctx, public);
}
```

and the session cannot be replaced by the statement alone, whose values
would then not be absorbed,

```compile_fail,E0308
use longfellow_zk::runtime::{
    algebra::{gf2_128::Gf2_128Field, range_interpolation::EvaluationDomain},
    v2::{
        proto::zk::ZkProof,
        transcript::Unverified,
        zk::{ZkContext, ZkProofStatement, ZkVerifier},
    },
};
fn verify<D: EvaluationDomain<2, Gf2_128Field>>(
    v: &ZkVerifier<2, Gf2_128Field>,
    statement: &ZkProofStatement<'_, 2, Gf2_128Field>,
    proof: Unverified<'_, ZkProof<2, Gf2_128Field>>,
    ctx: &ZkContext<'_, 2, Gf2_128Field, D>,
) {
    let _ = v.verify(statement, proof, ctx);
}
```

nor be opened with a geometry, which is no statement:

```compile_fail,E0277
use longfellow_zk::runtime::v2::{proto::zk::ZkProofGeometry, transcript::Opened};
fn open(geometry: &ZkProofGeometry) {
    let _ = Opened::new(geometry);
}
```
