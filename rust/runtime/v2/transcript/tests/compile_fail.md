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
