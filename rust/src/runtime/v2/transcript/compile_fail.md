A reader cannot send a message:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::{Reading, ZkStatement};
fn bad(mut r: Reading<'_>) { r.send(&ZkStatement { context: b"late" }); }
```

Only a statement writes setup messages: the header exists only while
`Transcript::new` runs, and it accepts no prover message.

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
use longfellow_zk::runtime::v2::transcript::{Transcript, ZkStatement};
let t = Transcript::new(&ZkStatement { context: b"context" });
```

Borrowed frontend operations cannot replace, clone or finalize their owner's
session:

```compile_fail,E0614
use longfellow_zk::runtime::v2::transcript::{Transcript, TranscriptRef, ZkStatement};
fn bad(mut t: TranscriptRef<'_>) { *t = Transcript::new(&ZkStatement { context: b"r" }); }
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
    transcript::Transcript,
    zk::{
        joint::{Bodies, Fields, Statements},
        JointVerifier,
    },
};
fn bad<L: Fields>(v: JointVerifier<L>, proof: &JointPolygeroProof<Bodies<L>>,
                  statements: Statements<L>, mut other: Transcript) {
    v.authenticate(proof, statements, &mut other);
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
