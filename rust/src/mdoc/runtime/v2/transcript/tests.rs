// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    mdoc::v2::{transcript::*, PolygeroParameters, ZkSpecStruct},
    runtime::v2::transcript::{Header, Statement, Transcript},
};

/// A statement that is the mdoc identity alone.
struct IdentityOnly<'a>(Identity<'a>);
impl<'a> Statement for IdentityOnly<'a> {
    type Identity = Identity<'a>;
    fn identity(&self) -> &Identity<'a> {
        &self.0
    }
    fn write(&self, _: &mut Header<'_>) {}
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
        polygero: p,
    }
}

/// `MdocStatement` writes the protocol ID, the session transcript, the
/// combined hash and (version, attribute count), in order.
#[test]
fn identity_has_its_documented_encoding() {
    let spec = spec([7; 32]);
    let t = Transcript::new(&IdentityOnly(Identity {
        session: b"session",
        spec: &spec,
    }));
    let le = |x: u64| x.to_le_bytes();
    let mut expected = le(16).to_vec();
    for b in [PROTOCOL_ID, b"session", &[7; 32]] {
        expected.extend(le(0));
        expected.extend(le(b.len() as u64));
        expected.extend(b);
    }
    expected.extend(le(1));
    expected.extend(le(2));
    for x in [7, 3] {
        expected.extend(le(x));
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
        }))
        .bytes(32)
    };
    let mut other = [7u8; 32];
    other[0] ^= 1;
    assert_ne!(draw([7; 32]), draw(other), "combined hash is not bound");
}
