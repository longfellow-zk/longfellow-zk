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

use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::{
            compile_v1 as compile, compile_v2, segment_circuit, CompilerAssertions, CompilerLogic,
        },
        logic::{Logic, LogicIO},
    },
    core::{
        algebra::{SerializableField, SupportsU64Conversions},
        proto::{compare_term, reader::CircuitReader, writer::CircuitWriter, FieldID},
    },
    runtime::algebra::RuntimeField,
};

// Exercise constants, linear terms, squares, products, and multiple layers.
fn build<F: CompileField>(
    logic: CompilerLogic<'_, F>,
) -> (CompilerAssertions<'_, F>, usize, usize) {
    let x: Vec<_> = (1..=8).map(|i| logic.input(i)).collect();
    let assertions = logic.assert_mapi("outputs", 0..8, |i| {
        let product = logic.mul(&x[i], &x[(i + 1) % 8]);
        let sum = logic.add(&product, &logic.mul(&x[(i + 2) % 8], &x[(i + 2) % 8]));
        let shifted = logic.add(&sum, &logic.one());
        let value = logic.mul(&shifted, &x[(i + 3) % 8]);
        logic.assert_eq("value", &logic.input(9 + i), &value)
    });
    (assertions, 4, 6)
}

fn check<const W: usize, FC, FR>(fc: &FC, fr: &FR, field_id: FieldID)
where
    FC: CompileField + SerializableField + Clone + SupportsU64Conversions,
    FR: RuntimeField<W> + SerializableField,
{
    let (legacy, legacy_geometry, _) = compile(fc, build);
    let (v2, v2_geometry, _) = compile_v2(fc, build);
    assert_eq!(legacy_geometry, v2_geometry);
    assert_eq!(v2.raw.subfield_boundary, 0);
    assert_eq!(legacy.raw.constants, v2.raw.constants);
    assert_ne!(legacy.id, v2.id, "fixture must distinguish the traversals");

    for (old_layer, new_layer) in legacy.raw.layers.iter().zip(&v2.raw.layers) {
        let old = old_layer.terms(&legacy.raw.constants);
        assert!(old
            .windows(2)
            .all(|pair| compare_term(fc, &pair[0], &pair[1]).is_lt()));
        let mut new = new_layer.terms(&v2.raw.constants);
        new.sort_by(|a, b| compare_term(fc, a, b));
        assert_eq!(old, new, "only traversal may differ, including wire IDs");
    }

    let writer = CircuitWriter::new(fc, field_id);
    let reader = CircuitReader::new(fr, field_id);
    for circuit in [&legacy, &v2] {
        let segmented = segment_circuit(fc, circuit);
        assert_eq!(circuit.id, segmented.id);
        let bytes = writer.to_bytes_lfc2(&segmented);
        let (runtime, tail) = reader.from_bytes(&bytes, true).unwrap();
        assert!(tail.is_empty());
        assert_eq!(runtime.id, circuit.id);

        for seed in 0..8 {
            let mut inputs = vec![fr.one()];
            let x: Vec<_> = (0..8)
                .map(|i| {
                    fr.bytes_to_element(&fc.to_bytes(&fc.u64_to_element(seed * 8 + i)))
                        .unwrap()
                })
                .collect();
            inputs.extend(x.iter().cloned());
            for i in 0..8 {
                let product = fr.mulf(&x[i], &x[(i + 1) % 8]);
                let sum = fr.addf(&product, &fr.mulf(&x[(i + 2) % 8], &x[(i + 2) % 8]));
                inputs.push(fr.mulf(&fr.addf(&sum, &fr.one()), &x[(i + 3) % 8]));
            }
            assert_eq!(runtime.raw.subfield_boundary,circuit.raw.subfield_boundary);
            if circuit.id == legacy.id {
                assert!(runtime.validate_v2().is_err());
                crate::runtime::sumcheck_v1::eval_circuit(inputs.clone(), &runtime, fr).unwrap();
            } else {
                crate::runtime::sumcheck_v2::eval_circuit(inputs.clone(), &runtime, fr).unwrap();
            }
            for i in 9..17 {
                let mut bad = inputs.clone();
                fr.add(&mut bad[i], &fr.one());
                assert!(
                    crate::runtime::sumcheck_v2::eval_circuit(bad.clone(), &runtime, fr).is_err()
                );
                if circuit.id == legacy.id {
                    assert!(crate::runtime::sumcheck_v1::eval_circuit(bad, &runtime, fr).is_err());
                }
            }
        }
    }
}

#[test]
fn legacy_morton_and_ng_preserve_wires_and_constraints_prime() {
    check(
        &crate::compile::algebra::p256::P256Field::new(),
        &crate::runtime::algebra::p256::P256Field::new(),
        FieldID::P256,
    );
}

#[test]
fn legacy_morton_and_ng_preserve_wires_and_constraints_binary() {
    check(
        &crate::compile::algebra::gf2_128::Gf2_128Field::new(),
        &crate::runtime::algebra::gf2_128::Gf2_128Field::new(),
        FieldID::Gf2_128,
    );
}
