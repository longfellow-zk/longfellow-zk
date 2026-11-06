// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Longfellow v2 codec roundtrips and malformed-proof rejection.

use crate::runtime::{
    algebra::AlgebraicField,
    v2::proto::sumcheck::{RoundPoly, SumcheckProof, SumcheckProofGeometry},
};

#[test]
fn single_hand_geometry_codec_and_malformed_shapes() {
    use crate::{core::algebra::SerializableField, runtime::v2::proto::sumcheck::LayerProof};
    let f = crate::runtime::algebra::p256::P256Field::new();
    let proof: SumcheckProof<4, _> = SumcheckProof {
        layers: vec![
            LayerProof {
                rounds: vec![
                    RoundPoly {
                        coefficients: [f.zero(), f.one()]
                    };
                    3
                ],
                cross: f.zero(),
                claims: [f.one(), f.zero()],
            },
            LayerProof {
                rounds: vec![],
                cross: f.zero(),
                claims: [f.zero(), f.one()],
            },
        ],
    };
    let geometry = proof.geometry();
    assert_eq!(geometry.serialized_elements().unwrap(), 12);
    let layout = geometry.pad_layout(7);
    assert_eq!(layout.layers[0].rounds[2], [11, 12]);
    assert_eq!(layout.layers[0].claims, [13, 14]);
    assert_eq!(layout.layers[1].claims, [17, 18]);
    let bytes = proof.write(&geometry, &f).unwrap();
    assert_eq!(bytes.len(), 12 * f.serialized_size_bytes());
    assert_eq!(
        SumcheckProof::read(&mut bytes.as_slice(), &geometry, &f).unwrap(),
        proof
    );
    for len in 0..bytes.len() {
        assert!(SumcheckProof::<4, _>::read(&mut &bytes[..len], &geometry, &f).is_err());
    }
    let invalid = SumcheckProofGeometry {
        logw_layers: vec![crate::runtime::v2::proto::sumcheck::MAX_LOGW + 1],
    };
    assert!(SumcheckProof::<4, _>::read(&mut bytes.as_slice(), &invalid, &f).is_err());
    let mut malformed = proof.clone();
    malformed.layers[0].rounds.pop();

    assert!(malformed.write(&geometry, &f).is_err());
}

#[test]
fn v2_codec_round_limit_is_inclusive_and_independent_of_host_width() {
    use crate::runtime::v2::proto::sumcheck::{pad_count, sane_logw, LayerProof, MAX_LOGW};
    let f = crate::runtime::algebra::p256::P256Field::new();
    for logw in [0, MAX_LOGW - 1, MAX_LOGW] {
        assert!(sane_logw(logw));
        let proof: SumcheckProof<4, _> = SumcheckProof {
            layers: vec![LayerProof {
                rounds: vec![
                    RoundPoly {
                        coefficients: [f.zero(), f.one()]
                    };
                    logw
                ],
                cross: f.zero(),
                claims: [f.one(), f.zero()],
            }],
        };
        let geometry = proof.geometry();
        assert_eq!(geometry.serialized_elements().unwrap(), 2 * logw + 3);
        let layout = geometry.pad_layout(7);
        assert_eq!(layout.layers[0].cross + 1, 7 + pad_count(logw));
        let bytes = proof.write(&geometry, &f).unwrap();
        let mut remaining = bytes.as_slice();
        assert_eq!(
            SumcheckProof::read(&mut remaining, &geometry, &f).unwrap(),
            proof
        );
        assert!(remaining.is_empty());
    }

    for logw in [MAX_LOGW + 1, usize::MAX] {
        assert!(!sane_logw(logw));
        let geometry = SumcheckProofGeometry {
            logw_layers: vec![logw],
        };
        assert!(geometry.serialized_elements().is_err());
        let input = [0u8; 32];
        let mut remaining = input.as_slice();
        assert!(SumcheckProof::<4, _>::read(&mut remaining, &geometry, &f).is_err());
        assert_eq!(remaining, input);
    }
    let too_many: SumcheckProof<4, _> = SumcheckProof {
        layers: vec![LayerProof {
            rounds: vec![
                RoundPoly {
                    coefficients: [f.zero(), f.one()]
                };
                MAX_LOGW + 1
            ],
            cross: f.zero(),
            claims: [f.one(), f.zero()],
        }],
    };
    assert!(too_many.write(&too_many.geometry(), &f).is_err());
}
