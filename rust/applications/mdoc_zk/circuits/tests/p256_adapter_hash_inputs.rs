// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::v2::{Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::algebra::gf2_128::Gf2_128Field,
};

fn fixture() -> RawCircuit<Gf2_128Field> {
    let f = Gf2_128Field::new();
    let ninput = 2 + super::super::AUXILIARY_BITS;
    RawCircuitBuilder {
        ninput,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        constants: vec![f.one(), f.zero()],
        layers: vec![Layer::with_assertions(
            ninput,
            Stream::<Quadratic>::from_terms([Quadratic {
                g: 0,
                l: 0,
                r: 1,
                k: 0,
            }]),
            Stream::<Linear>::from_terms([Linear { g: 0, l: 1, k: 1 }]),
            Stream::default(),
            |k| k == 1,
        )],
    }
    .build()
}

#[test]
fn hash_separation_rejects_mask_and_otp_reads_in_gates_and_assertions() {
    let circuit = fixture();
    validate(&circuit).unwrap();
    assert_eq!(
        super::super::AUXILIARY_BITS,
        super::super::MASK_BITS + super::super::shared_plan().advice_bits()
    );
    // First/last mask and OTP bits. Both factors and both coefficient classes
    // must be checked: a zero coefficient is an assertion, not a dead gate.
    for wire in [2, 2 + 255, 2 + 256, circuit.ninput - 1] {
        for k in [0, 1] {
            for right in [false, true] {
                let mut bad = fixture().into_builder();
                bad.layers[0].quadratic = Stream::<Quadratic>::from_terms([Quadratic {
                    g: 0,
                    l: if right { 0 } else { wire as u32 },
                    r: if right { wire as u32 } else { 1 },
                    k,
                }]);
                assert!(validate(&bad.build())
                    .unwrap_err()
                    .contains("reads adapter"));
            }
            let mut bad = fixture().into_builder();
            bad.layers[0].linear = Stream::<Linear>::from_terms([Linear {
                g: 0,
                l: wire as u32,
                k,
            }]);
            assert!(validate(&bad.build())
                .unwrap_err()
                .contains("reads adapter"));
        }
    }
}

#[test]
fn hash_separation_decodes_repeated_segments_before_checking_reads() {
    let mut circuit = fixture().into_builder();
    circuit.layers[0].linear = Stream {
        deltas: vec![Linear { g: 0, l: 1, k: 0 }],
        segments: vec![vec![0]].into(),
        tokens: vec![0],
    };
    let circuit = circuit.build();
    validate(&circuit).unwrap();
    let mut circuit = circuit.into_builder();
    // The same delta now addresses the first mask bit.
    circuit.layers[0].linear.tokens.push(0);
    assert!(validate(&circuit.build())
        .unwrap_err()
        .contains("reads adapter"));
}

#[test]
fn hash_separation_requires_a_private_suffix_and_input_layer() {
    let mut circuit = fixture().into_builder();
    circuit.npublic_input = 3;
    assert!(validate(&circuit.build()).is_err());
    circuit = fixture().into_builder();
    circuit.layers[0].nw -= 1;
    assert!(validate(&circuit.build()).is_err());
    circuit = fixture().into_builder();
    circuit.layers.clear();
    assert!(validate(&circuit.build()).is_err());
    circuit = fixture().into_builder();
    circuit.ninput = super::super::AUXILIARY_BITS - 1;
    assert!(validate(&circuit.build()).is_err());
}
