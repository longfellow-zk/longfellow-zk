//! Reindex LFC2 dictionaries without changing even the stored term traversal.
use core_algebra::SerializableField;
use core_proto::{
    circuit::{compute_id, Circuit, RawCircuit},
    FieldID, Layer, TermDelta,
};
use std::collections::HashMap;

fn key(d: &TermDelta, axes: [usize; 3], zigzag: bool) -> [u32; 4] {
    let coords = [d.g, d.h[0], d.h[1]];
    let enc = |x: u32| {
        if zigzag {
            (x << 1) ^ ((x as i32 >> 31) as u32)
        } else {
            x
        }
    };
    [
        enc(coords[axes[0]]),
        enc(coords[axes[1]]),
        enc(coords[axes[2]]),
        d.k_index,
    ]
}

pub(super) fn analyze<F: SerializableField + Clone>(f: &F, c: &Circuit<F>, field_id: FieldID) {
    let c = compile_compiler::segment_circuit(f, c);
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let mut global = HashMap::<TermDelta, usize>::new();
    for layer in &c.raw.layers {
        layer.for_each_delta(|d| *global.entry(*d).or_default() += 1);
    }
    let mut orders = vec![
        ("frequency".to_string(), [0, 1, 2], false),
        ("global_frequency".to_string(), [0, 1, 2], false),
    ];
    for axes in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        for zigzag in [false, true] {
            orders.push((
                format!(
                    "lex{}{}{}_z{}",
                    axes[0],
                    axes[1],
                    axes[2],
                    usize::from(zigzag)
                ),
                axes,
                zigzag,
            ));
        }
    }
    for (name, axes, zigzag) in orders {
        for segment_order in ["frequency", "lex", "length_lex"] {
            let mut layers = Vec::new();
            for layer in &c.raw.layers {
                let ds = layer.deltas();
                let mut indices: Vec<_> = (0..ds.len()).collect();
                if name == "global_frequency" {
                    indices.sort_unstable_by_key(|&i| {
                        (std::cmp::Reverse(global[&ds[i]]), key(&ds[i], axes, zigzag))
                    });
                } else if name != "frequency" {
                    indices.sort_unstable_by_key(|&i| key(&ds[i], axes, zigzag));
                }
                let mut remap = vec![0; ds.len()];
                for (new, &old) in indices.iter().enumerate() {
                    remap[old] = new as u32;
                }
                let ds = indices.iter().map(|&i| ds[i]).collect();
                let segments: Vec<Vec<u32>> = layer
                    .delta_segments()
                    .iter()
                    .map(|s| s.iter().map(|&i| remap[i as usize]).collect())
                    .collect();
                let mut indices: Vec<_> = (0..segments.len()).collect();
                if segment_order == "lex" {
                    indices.sort_unstable_by(|&a, &b| segments[a].cmp(&segments[b]));
                } else if segment_order == "length_lex" {
                    indices.sort_unstable_by(|&a, &b| {
                        segments[a]
                            .len()
                            .cmp(&segments[b].len())
                            .then_with(|| segments[a].cmp(&segments[b]))
                    });
                }
                let mut remap = vec![0; segments.len()];
                for (new, &old) in indices.iter().enumerate() {
                    remap[old] = new as u32;
                }
                let tokens = layer
                    .delta_tokens()
                    .iter()
                    .map(|&i| remap[i as usize])
                    .collect();
                let segments = indices.into_iter().map(|i| segments[i].clone()).collect();
                layers.push(Layer::new(layer.nw(), layer.logw(), ds, segments, tokens));
            }
            let candidate = Circuit {
                id: c.id,
                raw: RawCircuit {
                    ninput: c.raw.ninput,
                    npublic_input: c.raw.npublic_input,
                    noutput: c.raw.noutput,
                    logv: c.raw.logv,
                    subfield_boundary: c.raw.subfield_boundary,
                    constants: c.raw.constants.clone(),
                    layers,
                },
            };
            assert_eq!(compute_id(f, &candidate.raw), c.id);
            let bytes = writer.to_bytes_lfc2(&candidate);
            let (decoded, tail) = core_proto::reader::CircuitReader::new(f, field_id)
                .from_bytes_lfc2(&bytes, true)
                .unwrap();
            assert!(tail.is_empty());
            // Compare every decoded delta, not just a digest.
            for (a, b) in c.raw.layers.iter().zip(&decoded.raw.layers) {
                let mut expected = Vec::with_capacity(a.num_terms());
                a.for_each_delta(|d| expected.push(*d));
                let mut i = 0;
                b.for_each_delta(|d| {
                    assert_eq!(*d, expected[i]);
                    i += 1;
                });
                assert_eq!(i, expected.len());
            }
            println!("DICT deltas={name} segments={segment_order} raw={} zstd16={} exact_stream_and_id=true",
                bytes.len(), zstd::bulk::compress(&bytes, 16).unwrap().len());
        }
    }
}
