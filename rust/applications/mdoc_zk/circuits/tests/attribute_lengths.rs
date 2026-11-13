// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Full-capacity public attribute comparisons in the compiled v2 circuit.
use super::*;
use crate::compile::algebra::gf2_128::Gf2_128Field;

#[test]
fn compiled_attribute_checks_every_public_byte() {
    fn run<const N: usize>(prefix: &[u8]) {
        use crate::{
            circuits::bitvec::BitvecIO,
            core::{algebra::AlgebraicField},
            runtime::algebra::gf2_128::Gf2_128Field as RuntimeField,
        };
        let fc = Gf2_128Field::new();
        let fr = RuntimeField::new();
        let (circuit, _, symbols) = crate::compile::compiler::compile_v2(&fc, |logic| {
            let bits = BitvecLogic::new(&logic);
            let io = BitvecIO::new(&bits);
            let mut pos = crate::compile::logic::K_FIRST_WIRE_POSITION;
            let preimage: Vec<_> = (0..prefix.len() + N + 1)
                .map(|_| io.next::<8>(&mut pos))
                .collect();
            let public = AttrSlice::<_, N> {
                data: std::array::from_fn(|_| io.next::<8>(&mut pos)),
                len: io.next::<K_ATTR_INDEX_BITS>(&mut pos),
            };
            let slot_len = io.next::<K_ATTR_INDEX_BITS>(&mut pos);
            let locator = FieldLocator {
                slot_position: std::array::from_fn(|_| bits.of_u64(0)),
                length: std::array::from_fn(|_| slot_len.clone()),
                permutation: std::array::from_fn(|i| bits.of_u64(i as u64)),
            };
            (
                AttributeVerifier::new(&logic).assert_item_slot_key_value(
                    0,
                    &locator,
                    &preimage,
                    prefix.len() + N + 1,
                    prefix,
                    &public,
                ),
                1,
            )
        });
        let circuit = crate::compile::compiler::segment_circuit_v2(&fc, circuit);
        for length in 0..=N {
            let expected: Vec<u8> = (0..N).map(|i| (i * 17 + 33) as u8).collect();
            let mut raw = prefix.to_vec();
            raw.extend_from_slice(&expected[..length]);
            raw.resize(prefix.len() + N + 1, 0);
            let mut cases = vec![None];
            if length > 0 {
                for bit in 0..8 {
                    cases.push(Some((length - 1, bit)));
                }
            }
            if length == N {
                for byte in 0..N {
                    for bit in 0..8 {
                        cases.push(Some((byte, bit)));
                    }
                }
            }
            for changed in cases {
                let mut public = expected.clone();
                if let Some((byte, bit)) = changed {
                    public[byte] ^= 1 << bit;
                }
                let mut inputs = Vec::new();
                let mut push = |value: u64, width| {
                    for bit in 0..width {
                        inputs.push(if value >> bit & 1 == 1 {
                            fr.one()
                        } else {
                            fr.zero()
                        });
                    }
                };
                for byte in raw.iter().chain(&public) {
                    push(u64::from(*byte), 8);
                }
                push(length as u64, K_ATTR_INDEX_BITS);
                push((prefix.len() + length) as u64, K_ATTR_INDEX_BITS);
                let result = crate::compile::eval::eval_circuit_fc(&fc,
                    &fr,
                    &circuit,
                    &symbols,
                    &inputs)
                .unwrap();
                assert_eq!(
                    result.is_ok(),
                    changed.is_none(),
                    "N={N}, len={length}, mutation={changed:?}"
                );
            }
        }
    }
    run::<32>(&K_ELEMENT_IDENTIFIER_PREFIX);
    run::<64>(&K_ELEMENT_VALUE_PREFIX);
}
