// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    mdoc::v2::{transcript::*, PolygeroParameters, ZkSpecStruct},
    runtime::v2::transcript::{Header, Statement, Transcript},
};

struct IdentityOnly<'a>(Identity<'a>);
impl Statement for IdentityOnly<'_> {
    fn write(&self, h: &mut Header<'_>) {
        h.send(&self.0);
    }
}

fn spec(hash: [u8; 32]) -> ZkSpecStruct {
    let p = PolygeroParameters {
        k: 8,
        n: 64,
        s: 2,
        t: 2,
    };
    ZkSpecStruct {
        combined_hash: hash,
        num_attributes: 3,
        version: 7,
        polygero_hash: p,
        polygero_sig: p,
    }
}

/// `MdocStatement` writes the protocol ID, the session transcript, the
/// combined hash, (version, attribute count) and the profile, in order.
#[test]
fn identity_has_its_documented_encoding() {
    let spec = spec([7; 32]);
    let t = Transcript::new(&IdentityOnly(Identity {
        session: b"session",
        spec: &spec,
        profile: [8, 2, 64, 2],
    }));
    let le = |x: u64| x.to_le_bytes();
    let mut expected = le(16).to_vec();
    for b in [PROTOCOL_ID, b"session", &[7; 32]] {
        expected.extend(le(0));
        expected.extend(le(b.len() as u64));
        expected.extend(b);
    }
    for xs in [&[7u64, 3][..], &[8, 2, 64, 2]] {
        expected.extend(le(1));
        expected.extend(le(xs.len() as u64));
        for &x in xs {
            expected.extend(le(x));
        }
    }
    let node = t.preimage_for_test();
    assert!(node.ends_with(&expected));
    assert_eq!(node.len(), 16 + expected.len());
    assert_eq!(PROTOCOL_ID, b"longfellow/v2/mdoc/transcript/v2");
}

/// The spec's combined hash must change every later challenge.
#[test]
fn statement_binds_combined_hash() {
    let draw = |hash| {
        let spec = spec(hash);
        Transcript::new(&IdentityOnly(Identity {
            session: b"session",
            spec: &spec,
            profile: [8, 2, 64, 2],
        }))
        .bytes(32)
    };
    let mut other = [7u8; 32];
    other[0] ^= 1;
    assert_ne!(draw([7; 32]), draw(other), "combined hash is not bound");
}
