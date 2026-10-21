// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
use runtime_algebra::AlgebraicField;
use runtime_proto::sumcheck_ng::{RoundPoly, SumcheckProof, SumcheckProofGeometry};

#[test]
fn single_hand_geometry_codec_and_malformed_shapes() {
    use core_algebra::SerializableField;
    use runtime_proto::sumcheck_ng::LayerProof;
    let f = runtime_algebra::p256::P256Field::new();
    let proof: SumcheckProof<4, _> = SumcheckProof {
        layers: vec![
            LayerProof {
                rounds: vec![
                    RoundPoly {
                        evaluations: [f.zero(), f.one()]
                    };
                    3
                ],
                claims: [f.one(), f.zero()],
            },
            LayerProof {
                rounds: vec![],
                claims: [f.zero(), f.one()],
            },
        ],
    };
    let geometry = proof.geometry();
    assert_eq!(geometry.serialized_elements().unwrap(), 10);
    let layout = geometry.pad_layout(7);
    assert_eq!(layout.size, 12);
    assert_eq!(layout.layers[0].rounds[2], [11, 12]);
    assert_eq!(layout.layers[0].claims, [13, 14, 15]);
    assert_eq!(layout.layers[1].claims, [16, 17, 18]);
    let bytes = proof.write(&geometry, &f).unwrap();
    assert_eq!(bytes.len(), 10 * f.serialized_size_bytes());
    assert_eq!(
        SumcheckProof::read(&mut bytes.as_slice(), &geometry, &f).unwrap(),
        proof
    );
    for len in 0..bytes.len() {
        assert!(SumcheckProof::<4, _>::read(&mut &bytes[..len], &geometry, &f).is_err());
    }
    let invalid = SumcheckProofGeometry {
        logw_layers: vec![runtime_proto::sumcheck_ng::MAX_LOGW + 1],
    };
    assert!(SumcheckProof::<4, _>::read(&mut bytes.as_slice(), &invalid, &f).is_err());
    let mut malformed = proof.clone();
    malformed.layers[0].rounds.pop();

    assert!(malformed.write(&geometry, &f).is_err());
}
