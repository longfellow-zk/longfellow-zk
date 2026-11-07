A writer must be consumed before challenges can be sampled:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Writing;
fn bad(mut w: Writing<'_>) { w.bytes(32); }
```

The reader cannot bind messages or start another squeezing phase:

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Reading;
fn bad(mut r: Reading<'_>) { r.write_bytes(b"late"); }
```

```compile_fail,E0599
use longfellow_zk::runtime::v2::transcript::Reading;
fn bad(r: Reading<'_>) { r.begin_squeeze(); }
```

Neither phase can be reused after its transition:

```compile_fail,E0382
use longfellow_zk::runtime::v2::transcript::Writing;
fn bad(w: Writing<'_>) { let r = w.begin_squeeze(); let other = w.begin_squeeze(); }
```

```compile_fail,E0382
use longfellow_zk::runtime::v2::transcript::Reading;
fn bad(r: Reading<'_>) { let end = r.end_round(()); let other = r.end_round(()); }
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

Positive control: the permitted transitions compose and carry the original
round lifetime through its completion token.

```
use longfellow_zk::runtime::v2::transcript::{Writing, RoundEnd};
fn round(w: Writing<'_>) -> RoundEnd<'_, Vec<u8>> {
    let mut r = w.begin_squeeze();
    let challenge = r.bytes(32);
    r.end_round(challenge)
}
```

Borrowed frontend operations cannot replace, clone or finalize their owner's
session:

```compile_fail,E0614
use longfellow_zk::runtime::v2::transcript::{Transcript, TranscriptRef};
fn bad(mut t: TranscriptRef<'_>) { *t = Transcript::new(b"replacement"); }
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
    zk::joint::{Bodies, Fields, JointVerifier, Statements},
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
    algebra::{EvaluationDomain, ZkField},
    v2::zk::ZkContext,
};
fn bad<const W: usize, F: ZkField<W>, D: EvaluationDomain<W, F>>(f: &F, domain: &D) {
    let _ = ZkContext { f, domain };
}
```
