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

use core_algebra::AlgebraicField;
use core_proto::{
    circuit::{compute_canonical_id, compute_id, Circuit, RawCircuit},
    reader::CircuitReader,
    writer::CircuitWriter,
    FieldID, Layer, SerializableField, TermDelta,
};

fn layer<F: SerializableField>(terms: &[[u32; 4]]) -> Layer<F> {
    let mut previous = [0u32; 3];
    let deltas = terms
        .iter()
        .map(|&[g, h0, h1, k_index]| {
            let d = TermDelta {
                g: g.wrapping_sub(previous[0]),
                h: [h0.wrapping_sub(previous[1]), h1.wrapping_sub(previous[2])],
                k_index,
            };
            previous = [g, h0, h1];
            d
        })
        .collect();
    Layer::new_compressed(16, 4, vec![deltas], vec![0])
}

fn raw<F: SerializableField + AlgebraicField>(f: &F, terms: &[[u32; 4]]) -> RawCircuit<F> {
    RawCircuit {
        ninput: 16,
        npublic_input: 1,
        noutput: 3,
        logv: 2,
        subfield_boundary: 1,
        constants: vec![f.zero(), f.one(), f.neg(&f.one()), f.one()],
        layers: vec![layer(terms), layer(&[[0, 1, 2, 1]])],
    }
}

fn check<F: SerializableField + AlgebraicField + Clone>(f: &F, field_id: FieldID) {
    // Exact duplicates, different coefficients at the same coordinates, duplicate
    // constant values at different indices, assertions, and decreasing coordinates.
    let terms = vec![
        [2, 3, 7, 1],
        [0, 0, 0, 0],
        [2, 3, 7, 2],
        [1, 5, 1, 3],
        [2, 3, 7, 1],
    ];
    let original = raw(f, &terms);
    let expected = compute_canonical_id(f, &original);
    let old_id = compute_id(f, &original);
    let mut sorted = terms.clone();
    sorted.sort_by(|a, b| {
        a[..3].cmp(&b[..3]).then_with(|| {
            f.to_bytes(&original.constants[a[3] as usize])
                .cmp(&f.to_bytes(&original.constants[b[3] as usize]))
        })
    });
    // Independent reference: existing stream hash over explicitly sorted terms.
    assert_eq!(expected, compute_id(f, &raw(f, &sorted)));
    for shift in 0..terms.len() {
        let mut reordered = terms.clone();
        reordered.rotate_left(shift);
        reordered.reverse();
        let candidate = raw(f, &reordered);
        assert_eq!(compute_canonical_id(f, &candidate), expected);
    }
    let mut reversed = terms.clone();
    reversed.reverse();
    assert_ne!(old_id, compute_id(f, &raw(f, &reversed)));
    assert_eq!(old_id, compute_id(f, &original));

    let mut renumbered = raw(f, &terms);
    renumbered.constants.reverse();
    for l in &mut renumbered.layers {
        for d in l.deltas_mut() {
            d.k_index = 3 - d.k_index;
        }
    }
    renumbered.constants.push(f.zero()); // Unused constants do not affect the ID.
    assert_eq!(compute_canonical_id(f, &renumbered), expected);

    let circuit = Circuit {
        raw: original,
        id: old_id,
    };
    let segmented = compile_compiler::segment_circuit(f, &circuit);
    let writer = CircuitWriter::new(f, field_id);
    for bytes in [
        writer.to_bytes_lfc1(&segmented),
        writer.to_bytes_lfc2(&segmented),
    ] {
        let (decoded, tail) = CircuitReader::new(f, field_id)
            .from_bytes(&bytes, true)
            .unwrap();
        assert!(tail.is_empty());
        assert_eq!(decoded.id, old_id);
        assert_eq!(compute_canonical_id(f, &decoded.raw), expected);
    }

    for changed_index in 0..4 {
        let mut changed = terms.clone();
        changed[1][changed_index] += 1;
        assert_ne!(compute_canonical_id(f, &raw(f, &changed)), expected);
    }
    // Dropping a duplicate, swapping layers, or changing geometry is not invariant.
    assert_ne!(compute_canonical_id(f, &raw(f, &terms[..4])), expected);
    let mut changed_layers = raw(f, &terms);
    changed_layers.layers.swap(0, 1);
    assert_ne!(compute_canonical_id(f, &changed_layers), expected);
    for which in 0..8 {
        let mut changed = raw(f, &terms);
        match which {
            0 => changed.ninput += 1,
            1 => changed.npublic_input += 1,
            2 => changed.noutput += 1,
            3 => changed.logv += 1,
            4 => changed.subfield_boundary += 1,
            5 => changed.layers.push(layer(&[])),
            6 => changed.layers[0] = Layer::new_compressed(17, 4, vec![], vec![]),
            _ => changed.layers[0] = Layer::new_compressed(16, 5, vec![], vec![]),
        }
        assert_ne!(compute_canonical_id(f, &changed), expected);
    }
    let mut empty = raw(f, &[]);
    assert_eq!(compute_canonical_id(f, &empty), compute_id(f, &empty));
    empty.layers.clear();
    assert_eq!(compute_canonical_id(f, &empty), compute_id(f, &empty));

    // Cross hash-buffer boundaries, with a second layer following the partial buffer.
    let many: Vec<_> = (0..1000u32)
        .map(|i| [i % 3, (i * 7) % 16, (i * 11) % 16, i % 4])
        .collect();
    let many_raw = raw(f, &many);
    let mut canonical = many;
    canonical.sort_by(|a, b| {
        a[..3].cmp(&b[..3]).then_with(|| {
            f.to_bytes(&many_raw.constants[a[3] as usize])
                .cmp(&f.to_bytes(&many_raw.constants[b[3] as usize]))
        })
    });
    assert_eq!(
        compute_canonical_id(f, &many_raw),
        compute_id(f, &raw(f, &canonical)),
    );
}

#[test]
fn canonical_id_prime_field() {
    check(&compile_algebra::p256::P256Field::new(), FieldID::P256);
}

#[test]
fn canonical_id_binary_field() {
    check(
        &compile_algebra::gf2_128::Gf2_128Field::new(),
        FieldID::Gf2_128,
    );
}
