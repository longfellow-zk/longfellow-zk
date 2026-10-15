// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
//! Fixed-geometry scheduling x segmentation sweep. Trusted offline fixtures only.
#[path = "../../../experiments/mldsa/segment_dictionary.rs"]
mod dictionary;
#[allow(dead_code)]
#[path = "layer_templates.rs"]
mod existing;
#[path = "../../../experiments/mldsa/segment_extract.rs"]
mod extract;
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/pair_segments.rs"]
mod pairs;
#[path = "../../../experiments/mldsa/segmentation_policies.rs"]
mod policies;
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/segment_window.rs"]
mod window;

use core_proto::{
    FieldID, SerializableField,
    circuit::{Circuit, RawCircuit, compute_id},
};
use std::{path::PathBuf, time::Instant};

fn segment_base<F: SerializableField + Clone>(
    layer: &core_proto::Layer<F>,
    policy: &str,
) -> core_proto::Layer<F> {
    if let Some((mode, base)) = policy.split_once('@') {
        if let Some(mode) = mode.strip_prefix("extract") {
            return extract::extract(segment_base(layer, base), mode);
        }
        return dictionary::reorder(
            segment_base(layer, base),
            mode.strip_prefix("dict").unwrap(),
        );
    }
    if policy == "reuse" {
        return existing::reusable_interiors_with_base(layer, 32, window::segment_layer(layer, 32));
    }
    if let Some(base) = policy.strip_prefix("reuse_") {
        return existing::reusable_interiors_with_base(layer, 32, segment_base(layer, base));
    }
    if let Some(w) = policy.strip_prefix("window_") {
        window::segment_layer(layer, w.parse().unwrap())
    } else if let Some(p) = policy.strip_prefix("pair_") {
        if let Some(p) = p.strip_prefix("stock_") {
            pairs::segment(&window::segment_layer(layer, 64), &format!("seed_{p}"))
        } else if let Some(p) = p.strip_prefix("cdc_") {
            pairs::segment(&policies::segment(layer, "cdc_128"), &format!("seed_{p}"))
        } else {
            pairs::segment(layer, p)
        }
    } else {
        policies::segment(layer, policy)
    }
}

fn run<F: SerializableField + core_algebra::AlgebraicField + Clone>(
    name: &str,
    f: &F,
    field: FieldID,
) {
    let wire = std::env::var("SWEEP_WIRE").unwrap();
    let traversal = std::env::var("SWEEP_TRAVERSAL").unwrap();
    let output = PathBuf::from(std::env::var("SWEEP_OUTPUT").unwrap());
    std::fs::create_dir_all(&output).unwrap();
    let bytes = std::fs::read(std::env::var("ORDER_INPUT_CIRCUIT").unwrap()).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let (source, tail) = reader.from_bytes(&bytes, true).unwrap();
    assert!(tail.is_empty());
    let start = Instant::now();
    let renamed = if wire == "none" {
        source
    } else {
        existing::morton::template_wires::renumber(f, &source, &wire)
    };
    let ordered = match traversal.as_str() {
        "shape" => existing::morton::template_wires::shape_order(f, &renamed),
        "morton" => existing::morton::absolute_morton_control(f, &renamed),
        "shape_classes" | "shape_terms" => {
            existing::morton::layer_template_control(f, &renamed, 4, &traversal)
        }
        _ => panic!("unknown traversal"),
    };
    existing::builder::assert_same(&renamed, &ordered);
    drop(renamed);
    let layout_ms = start.elapsed().as_secs_f64() * 1000.;
    let writer = core_proto::writer::CircuitWriter::new(f, field);
    let lfc1 = writer.to_bytes_lfc1(&ordered);
    println!(
        "SWEEP_LAYOUT dataset={name} wire={wire} traversal={traversal} terms={} wires={} layers={} lfc1={} lfc1z16={} layout_ms={layout_ms:.3}",
        ordered
            .raw
            .layers
            .iter()
            .map(|l| l.num_terms())
            .sum::<usize>(),
        ordered.raw.noutput + ordered.raw.layers.iter().map(|l| l.nw()).sum::<usize>(),
        ordered.raw.layers.len(),
        lfc1.len(),
        zstd::bulk::compress(&lfc1, 16).unwrap().len()
    );
    drop(lfc1);
    let modes = std::env::var("SWEEP_SEGMENTS").unwrap_or_else(|_| {
        "standard,reuse,window_16,window_64,window_128,fixed_32,fixed_128,cdc_32,cdc_128,allphase_32,allphase_64,cdcstored_64".into()
    });
    for policy in modes.split(',') {
        let start = Instant::now();
        let c = if matches!(policy, "standard" | "reuse") {
            existing::repack(&ordered, policy)
        } else {
            let layers = ordered
                .raw
                .layers
                .iter()
                .map(|layer| {
                    if let Some(base_policy) = policy.strip_prefix("reuse_") {
                        let base = segment_base(layer, base_policy);
                        existing::reusable_interiors_with_base(layer, 32, base)
                    } else {
                        segment_base(layer, policy)
                    }
                })
                .collect();
            Circuit {
                raw: RawCircuit {
                    layers,
                    ninput: ordered.raw.ninput,
                    npublic_input: ordered.raw.npublic_input,
                    noutput: ordered.raw.noutput,
                    logv: ordered.raw.logv,
                    subfield_boundary: ordered.raw.subfield_boundary,
                    constants: ordered.raw.constants.clone(),
                },
                id: ordered.id,
            }
        };
        let segment_ms = start.elapsed().as_secs_f64() * 1000.;
        let bytes = writer.to_bytes_lfc2(&c);
        let (decoded, tail) = reader.from_bytes(&bytes, true).unwrap();
        assert!(tail.is_empty());
        assert_eq!(compute_id(f, &decoded.raw), ordered.id);
        assert_eq!(writer.to_bytes_lfc2(&decoded), bytes);
        assert_eq!(decoded.raw.ninput, ordered.raw.ninput);
        assert_eq!(decoded.raw.npublic_input, ordered.raw.npublic_input);
        assert_eq!(decoded.raw.noutput, ordered.raw.noutput);
        assert_eq!(decoded.raw.subfield_boundary, ordered.raw.subfield_boundary);
        assert_eq!(decoded.raw.layers.len(), ordered.raw.layers.len());
        for (a, b) in ordered.raw.layers.iter().zip(&decoded.raw.layers) {
            assert_eq!(a.nw(), b.nw());
            assert_eq!(a.logw(), b.logw());
            let mut expected = Vec::with_capacity(a.num_terms());
            a.for_each_delta(|d| expected.push(*d));
            let mut i = 0;
            b.for_each_delta(|d| {
                assert_eq!(*d, expected[i]);
                i += 1;
            });
            assert_eq!(i, expected.len());
        }
        let z16 = zstd::bulk::compress(&bytes, 16).unwrap().len();
        let z22 = if std::env::var_os("SWEEP_Z22").is_some() {
            zstd::bulk::compress(&bytes, 22).unwrap().len()
        } else {
            0
        };
        println!(
            "SWEEP_SIZE dataset={name} wire={wire} traversal={traversal} segmentation={policy} raw={} z16={z16} z22={z22} deltas={} segments={} entries={} tokens={} segment_ms={segment_ms:.3} exact=true",
            bytes.len(),
            c.raw.layers.iter().map(|l| l.deltas().len()).sum::<usize>(),
            c.raw
                .layers
                .iter()
                .map(|l| l.delta_segments().len())
                .sum::<usize>(),
            c.raw
                .layers
                .iter()
                .flat_map(|l| l.delta_segments())
                .map(Vec::len)
                .sum::<usize>(),
            c.raw
                .layers
                .iter()
                .map(|l| l.delta_tokens().len())
                .sum::<usize>()
        );
        std::fs::write(output.join(format!("{policy}.lfc2")), bytes).unwrap();
    }
}

#[test]
#[ignore = "offline complete layout and segmentation matrix"]
fn scheduling_segmentation_sweep() {
    let name = std::env::var("ORDER_DATASET").unwrap();
    match name.as_str() {
        "mdoc_hash2" => run(
            &name,
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            FieldID::Gf2_128,
        ),
        "mdoc_sig" => run(
            &name,
            &runtime_algebra::p256::P256Field::new(),
            FieldID::P256,
        ),
        "mldsa44" | "mldsa65" => run(
            &name,
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            FieldID::None,
        ),
        _ => panic!("unknown dataset"),
    }
}
