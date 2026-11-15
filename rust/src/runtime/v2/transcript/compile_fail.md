A reader cannot send a message:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::{Reading, ZkStatement};
fn bad(mut r: Reading<'_>) { r.send(&ZkStatement { context: b"late" }); }
```

Only a statement writes setup messages: the header exists only while a
session opens, and it accepts no prover message.

```compile_fail,E0451
use longfellow_zk::runtime::v2::transcript::{Header, Transcript};
fn bad(t: &mut Transcript) -> Header<'_> { Header { session: t } }
```

```compile_fail,E0277
use longfellow_zk::runtime::v2::transcript::{Header, ProverMessage};
fn bad<M: ProverMessage>(h: &mut Header<'_>, m: &M) { h.send(m); }
```

Sessions cannot be cloned, sampled as private randomness, or finalized with
caller-selected raw bytes:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Transcript;
fn bad(t: Transcript) { let other = t.clone(); }
```

```compile_fail,E0277
use longfellow_zk::runtime::{random::RandomEngine, v2::transcript::Reading};
fn witness_rng(_: &mut impl RandomEngine) {}
fn bad(mut r: Reading<'_>) { witness_rng(&mut r); }
```

```compile_fail,E0624
use longfellow_zk::runtime::v2::transcript::Transcript;
fn bad(t: Transcript) { t.append_final_seal(vec![]); }
```

Verification evidence and encoded proofs have private construction:

```compile_fail
use longfellow_zk::runtime::v2::transcript::VerifiedProof;
fn bad() -> VerifiedProof { VerifiedProof { _private: () } }
```

```compile_fail,E0423
use longfellow_zk::runtime::v2::transcript::EncodedProof;
fn bad() -> EncodedProof { EncodedProof(vec![]) }
```

A parsed proof is immutable:

```compile_fail,E0594
use longfellow_zk::runtime::v2::transcript::Unverified;
fn bad(mut proof: Unverified<'_, u8>) { *proof = 42; }
```

Positive control: a statement opens a session.

```
use longfellow_zk::runtime::v2::transcript::{Opened, ZkStatement};
let statement = ZkStatement { context: b"context" };
let session = Opened::new(&statement);
```

Outside the crate a session opens only with the statement it keeps
(`Opened::new`):

```compile_fail,E0624
use longfellow_zk::runtime::v2::transcript::{Transcript, ZkStatement};
let t = Transcript::new(&ZkStatement { context: b"context" });
```

Borrowed frontend operations cannot replace, clone or finalize their owner's
session:

```compile_fail,E0614
use longfellow_zk::runtime::v2::transcript::{Transcript, TranscriptRef};
fn bad(mut t: TranscriptRef<'_>) { *t = Transcript::for_test(b"r"); }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::TranscriptRef;
fn bad(t: TranscriptRef<'_>) { let other = t.clone(); }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::TranscriptRef;
fn bad(t: TranscriptRef<'_>) { t.append_final_seal(vec![]); }
```

Receiving a joint commitment transfers ownership of the session:

```compile_fail,E0382
use longfellow_zk::runtime::v2::{
    proto::polygero::PolygeroCommitment,
    transcript::Transcript,
    zk::joint::{Fields, JointParam, Responses},
};
fn bad<L: Fields>(p: JointParam<L>, root: &PolygeroCommitment,
                  responses: Responses<L>, t: Transcript) {
    let session = p.receive(root, responses, t);
    drop(t);
}
```

Late authentication cannot take a replacement transcript:

```compile_fail,E0061
use longfellow_zk::runtime::v2::{
    proto::polygero::JointPolygeroProof,
    transcript::{Challenge, Transcript},
    zk::{
        joint::{Bodies, Fields, Statements, Weights},
        JointVerifier,
    },
};
fn bad<L: Fields>(v: JointVerifier<L>, batch: Challenge<Weights<L>>,
                  proof: &JointPolygeroProof<Bodies<L>>, statements: Statements<L>,
                  mut other: Transcript) {
    v.authenticate(batch, proof, statements, &mut other);
}
```

The field in a v2 context comes from its domain, rather than an independent
struct member:

```compile_fail,E0560
use longfellow_zk::runtime::{
    algebra::{range_interpolation::EvaluationDomain, ZkField},
    v2::zk::ZkContext,
};
fn bad<const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>>(f: &F, domain: &D) {
    let _ = ZkContext { f, domain };
}
```

Elements carry only registered fields (`RegisteredField`), whose FieldID
names one field and one encoding width. GF(2) and GF(256) share
`FieldID::None` and the same one-byte encoding of one, and the P-256
scalar field has no registered ID, so none of them can be absorbed:

```compile_fail,E0277
use longfellow_zk::runtime::{
    algebra::packing::binary::Gf2,
    v2::{proto::tags::Tag, transcript::{Encoder, Message}},
};
struct One;
impl Message for One {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) { e.elements(&Gf2, &[true]); }
}
```

```compile_fail,E0277
use longfellow_zk::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::packing::binary::Gf256,
        v2::{proto::tags::Tag, transcript::{Encoder, Message}},
    },
};
struct One;
impl Message for One {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        let f = Gf256::new();
        e.elements(&f, &[f.one()]);
    }
}
```

```compile_fail,E0277
use longfellow_zk::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::q256::Q256Field,
        v2::{proto::tags::Tag, transcript::{Encoder, Message}},
    },
};
struct One;
impl Message for One {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        let f = Q256Field::new();
        e.elements(&f, &[f.one()]);
    }
}
```

Positive control: P-256 and GF(2^128) are registered.

```
use longfellow_zk::{
    core::algebra::AlgebraicField,
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field},
        v2::{proto::tags::Tag, transcript::{Encoder, Message}},
    },
};
struct Ones;
impl Message for Ones {
    const TAG: Tag = Tag::PublicInputs;
    fn encode(&self, e: &mut Encoder<'_>) {
        let (p, b) = (P256Field::new(), Gf2_128Field::new());
        e.elements(&p, &[p.one()]);
        e.elements(&b, &[b.one()]);
    }
}
```

A stream is read only by the four allocation-free draw kinds: `elt_field`,
`nonzero`, `elements` (yielded to the caller) and `choose` (in the caller's
scratch). Raw bytes and allocating vectors are test-only:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Reading;
fn bad(r: &mut Reading<'_>) -> Vec<u8> { r.bytes(16) }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Reading;
fn bad(r: &mut Reading<'_>, out: &mut [u8]) { r.fill(out) }
```

```compile_fail,E0599
use longfellow_zk::runtime::{algebra::p256::P256Field, v2::transcript::Reading};
fn bad(r: &mut Reading<'_>, f: &P256Field) { let _ = r.elt_field_slice(3, f); }
```

Positive control: the four draw kinds.

```
use longfellow_zk::runtime::{algebra::p256::P256Field, v2::transcript::Reading};
fn draws(r: &mut Reading<'_>, f: &P256Field) {
    let _ = r.elt_field(f);
    let _ = r.nonzero(f);
    let _: Vec<_> = r.elements(f, 3).collect();
    let (mut out, mut scratch) = ([0; 2], [0; 8]);
    r.choose(&mut out, 8, &mut scratch);
}
```
