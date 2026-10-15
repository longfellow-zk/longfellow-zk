// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Offline template-guided ordering; every saved artifact is ordinary LFC2.
#[path = "../../../experiments/mldsa/layer_templates.rs"]
pub(crate) mod builder;
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/morton.rs"]
pub(crate) mod morton;

use core_proto::{
    circuit::{Circuit, RawCircuit},
    FieldID, Layer, SerializableField,
};
use std::{collections::HashMap, time::Instant};

fn boundary_segments<F: SerializableField>(layer: &Layer<F>, width: usize) -> Layer<F> {
    assert!(width > 0);
    let mut dictionary = HashMap::<Vec<u32>, u32>::new();
    let mut segments = Vec::<Vec<u32>>::new();
    let mut tokens = Vec::new();
    let mut push = |run: &[u32]| {
        if run.is_empty() {
            return;
        }
        let id = if let Some(&id) = dictionary.get(run) {
            id
        } else {
            let id = segments.len() as u32;
            dictionary.insert(run.to_vec(), id);
            segments.push(run.to_vec());
            id
        };
        tokens.push(id);
    };
    // The scheduler's initial runs are exact template instances, with global
    // coordinate differencing already applied continuously across boundaries.
    for &token in layer.delta_tokens() {
        let run = &layer.delta_segments()[token as usize];
        if let Some((_, body)) = run.split_first() {
            push(&run[..1]);
            for chunk in body.chunks(width) {
                push(chunk);
            }
        }
    }
    frequency_segments(layer, segments, tokens)
}

fn frequency_segments<F: SerializableField>(
    layer: &Layer<F>,
    mut segments: Vec<Vec<u32>>,
    mut tokens: Vec<u32>,
) -> Layer<F> {
    let mut segment_counts = vec![0usize; segments.len()];
    for &token in &tokens {
        segment_counts[token as usize] += 1;
    }
    let mut counts = vec![0usize; layer.deltas().len()];
    for (segment, &count) in segments.iter().zip(&segment_counts) {
        for &delta in segment {
            counts[delta as usize] += count;
        }
    }
    let mut order: Vec<_> = (0..counts.len()).collect();
    order.sort_unstable_by_key(|&i| (std::cmp::Reverse(counts[i]), i));
    let mut remap = vec![0u32; counts.len()];
    let deltas = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            remap[old] = new as u32;
            layer.deltas()[old]
        })
        .collect();
    for segment in &mut segments {
        for delta in segment {
            *delta = remap[*delta as usize];
        }
    }
    let mut order: Vec<_> = (0..segments.len()).collect();
    order.sort_unstable_by_key(|&i| (std::cmp::Reverse(segment_counts[i]), i));
    let mut remap = vec![0u32; segments.len()];
    let segments = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            remap[old] = new as u32;
            std::mem::take(&mut segments[old])
        })
        .collect();
    for token in &mut tokens {
        *token = remap[*token as usize];
    }
    Layer::new(layer.nw(), layer.logw(), deltas, segments, tokens)
}

// Replace repeated exact template interiors with one segment each. Leave the
// standard segmentation outside those spans intact (split only at span edges).
// The existing "reuse" profile requires a 32-term body; "reuse1" also shares
// shorter bodies. No measured-size chooser or circuit-specific rule.
fn reusable_interiors<F: SerializableField + Clone>(layer: &Layer<F>, min_body: usize) -> Layer<F> {
    assert!(min_body > 0);
    let base = compile_compiler::segment_layer(layer);
    reusable_interiors_with_base(layer, min_body, base)
}

pub(crate) fn reusable_interiors_with_base<F: SerializableField + Clone>(
    layer: &Layer<F>, min_body: usize, base: Layer<F>,
) -> Layer<F> {
    assert!(min_body > 0);
    let mut counts = HashMap::<&[u32], usize>::new();
    for &token in layer.delta_tokens() {
        let run = &layer.delta_segments()[token as usize];
        if run.len() > min_body {
            *counts.entry(&run[1..]).or_default() += 1;
        }
    }
    let mut spans = Vec::new();
    let mut offset = 0;
    for &token in layer.delta_tokens() {
        let run = &layer.delta_segments()[token as usize];
        if run.len() > min_body && counts[&run[1..]] > 1 {
            spans.push((offset + 1, offset + run.len()));
        }
        offset += run.len();
    }
    if spans.is_empty() {
        return base;
    }
    let mut stream = Vec::with_capacity(base.num_terms());
    let mut boundaries = Vec::new();
    for &token in base.delta_tokens() {
        stream.extend(&base.delta_segments()[token as usize]);
        boundaries.push(stream.len());
    }
    let mut dictionary = HashMap::<Vec<u32>, u32>::new();
    let mut segments = Vec::new();
    let mut tokens = Vec::new();
    let mut push = |slice: &[u32]| {
        if slice.is_empty() {
            return;
        }
        let next = segments.len() as u32;
        let id = *dictionary.entry(slice.to_vec()).or_insert_with(|| {
            segments.push(slice.to_vec());
            next
        });
        tokens.push(id);
    };
    let mut cursor = 0;
    let mut boundary = 0;
    let mut copy_to = |cursor: &mut usize, end: usize, push: &mut dyn FnMut(&[u32])| {
        while *cursor < end {
            while boundaries[boundary] <= *cursor {
                boundary += 1;
            }
            let next = end.min(boundaries[boundary]);
            push(&stream[*cursor..next]);
            *cursor = next;
        }
    };
    for &(start, end) in &spans {
        copy_to(&mut cursor, start, &mut push);
        push(&stream[start..end]);
        cursor = end;
    }
    copy_to(&mut cursor, stream.len(), &mut push);
    println!(
        "WIRE_SEGMENT_REUSE layer_terms={} occurrences={} covered_terms={}",
        stream.len(),
        spans.len(),
        spans.iter().map(|(a, b)| b - a).sum::<usize>()
    );
    frequency_segments(&base, segments, tokens)
}

// Preserve the ULEB length of every reference while clustering related entries.
// No term order, segmentation, dictionary cardinality, or raw byte count changes.
fn clustered_dictionary<F: SerializableField>(layer: &Layer<F>, both: bool) -> Layer<F> {
    let bucket = |i: usize| core_proto::writer::lfc2::uleb128_len_u32(i as u32);
    let zig = |n: u32| (((n as i32) << 1) ^ (n as i32 >> 31)) as u32;
    let mut order: Vec<_> = (0..layer.deltas().len()).collect();
    order.sort_unstable_by_key(|&i| {
        let d = layer.deltas()[i];
        (bucket(i), zig(d.g), zig(d.h[0]), zig(d.h[1]), d.k_index)
    });
    let mut remap = vec![0u32; order.len()];
    let deltas = order
        .iter()
        .enumerate()
        .map(|(new, &old)| {
            remap[old] = new as u32;
            layer.deltas()[old]
        })
        .collect();
    let mut segments: Vec<Vec<u32>> = layer
        .delta_segments()
        .iter()
        .map(|s| s.iter().map(|&d| remap[d as usize]).collect())
        .collect();
    let mut tokens = layer.delta_tokens().to_vec();
    if both {
        let mut order: Vec<_> = (0..segments.len()).collect();
        order.sort_unstable_by(|&a, &b| {
            bucket(a)
                .cmp(&bucket(b))
                .then(segments[a].cmp(&segments[b]))
        });
        let mut remap = vec![0u32; order.len()];
        segments = order
            .iter()
            .enumerate()
            .map(|(new, &old)| {
                remap[old] = new as u32;
                std::mem::take(&mut segments[old])
            })
            .collect();
        for token in &mut tokens {
            *token = remap[*token as usize];
        }
    }
    Layer::new(layer.nw(), layer.logw(), deltas, segments, tokens)
}

pub(crate) fn repack<F: SerializableField + Clone>(c: &Circuit<F>, mode: &str) -> Circuit<F> {
    let layers = c
        .raw
        .layers
        .iter()
        .map(|layer| match mode {
            "standard" => compile_compiler::segment_layer(layer),
            "reuse" => reusable_interiors(layer, 32),
            "reuse1" => reusable_interiors(layer, 1),
            "lex" => clustered_dictionary(layer, false),
            "lexboth" => clustered_dictionary(layer, true),
            _ => boundary_segments(
                layer,
                mode.strip_prefix("boundary").unwrap().parse().unwrap(),
            ),
        })
        .collect();
    Circuit {
        raw: RawCircuit {
            ninput: c.raw.ninput,
            npublic_input: c.raw.npublic_input,
            noutput: c.raw.noutput,
            logv: c.raw.logv,
            subfield_boundary: c.raw.subfield_boundary,
            constants: c.raw.constants.clone(),
            layers,
        },
        id: c.id,
    }
}

fn run<F: SerializableField + core_algebra::AlgebraicField + Clone>(
    name: &str,
    f: &F,
    field: FieldID,
) {
    let path = std::env::var("ORDER_INPUT_CIRCUIT")
        .unwrap_or_else(|_| format!("target/traversal-circuits/{name}--kind_abs_lex0213_r5.lfc2"));
    let input = std::fs::read(path).unwrap();
    let reader = core_proto::reader::CircuitReader::new(f, field);
    let reader = if let Ok(limit) = std::env::var("ORDER_TOTAL_TERM_LIMIT") {
        reader.with_total_term_limit(limit.parse().unwrap())
    } else {
        reader
    };
    let (c, tail) = reader.from_bytes(&input, true).unwrap();
    assert!(tail.is_empty());
    if std::env::var_os("ORDER_LAYER_STATS").is_some() {
        for (index, layer) in c.raw.layers.iter().enumerate() {
            println!("WIRE_LAYER dataset={name} input_depth={} inputs={} terms={} deltas={} segments={} segment_entries={} tokens={}",
                c.raw.layers.len()-1-index,layer.nw(),layer.num_terms(),layer.deltas().len(),
                layer.delta_segments().len(),layer.delta_segments().iter().map(Vec::len).sum::<usize>(),layer.delta_tokens().len());
        }
        return;
    }
    println!(
        "ORDER_BASE dataset={name} raw={} z16={} z22={} deltas={} terms={} wires={} layers={}",
        input.len(),
        zstd::bulk::compress(&input, 16).unwrap().len(),
        zstd::bulk::compress(&input, 22).unwrap().len(),
        c.raw.layers.iter().map(|l| l.deltas().len()).sum::<usize>(),
        c.raw.layers.iter().map(|l| l.num_terms()).sum::<usize>(),
        c.raw.noutput + c.raw.layers.iter().map(|l| l.nw()).sum::<usize>(),
        c.raw.layers.len()
    );
    let wire = std::env::var("ORDER_WIRE_POLICY").unwrap_or_else(|_| "none".into());
    let c = if wire == "none" {
        c
    } else {
        morton::template_wires::renumber(f, &c, &wire)
    };
    let components = std::env::var("ORDER_COMPONENTS").unwrap_or_else(|_| "3".into());
    let orders = std::env::var("ORDER_LOCAL_ORDERS").unwrap_or_else(|_| "4".into());
    let windows = std::env::var("ORDER_WINDOWS").unwrap_or_else(|_| "10000000".into());
    let modes = std::env::var("ORDER_SEGMENTS")
        .unwrap_or_else(|_| "standard,boundary32,boundary128".into());
    let traversals = std::env::var("ORDER_TRAVERSALS").unwrap_or_else(|_| "instances".into());
    let writer = core_proto::writer::CircuitWriter::new(f, field);
    for traversal in traversals.split(',') {
        for component in components.split(',').map(|s| s.parse().unwrap()) {
            for window in windows.split(',').map(|s| s.parse().unwrap()) {
                for order in orders.split(',').map(|s| s.parse().unwrap()) {
                    let start = Instant::now();
                    let ordered = if component == 6 {
                        assert_eq!(
                            wire, "none",
                            "vanilla Morton control preserves original wires"
                        );
                        morton::absolute_morton_control(f, &c)
                    } else if component == 5 {
                        morton::template_wires::shape_order(f, &c)
                    } else if component == 4 {
                        assert_eq!(
                            wire, "none",
                            "dictionary-only control requires original circuit"
                        );
                        reader.from_bytes(&input, true).unwrap().0
                    } else if component == 3 {
                        morton::layer_template_control(f, &c, order, traversal)
                    } else {
                        builder::convert(f, &c, window, false, order, component, traversal)
                    };
                    let build_ms = start.elapsed().as_secs_f64() * 1000.;
                    builder::assert_same(&c, &ordered);
                    let lfc1 = writer.to_bytes_lfc1(&ordered);
                    println!("ORDER_LFC1 dataset={name} wire={wire} components={component} window={window} order={order} traversal={traversal} raw={} z22={}",lfc1.len(),zstd::bulk::compress(&lfc1,22).unwrap().len());
                    drop(lfc1);
                    for mode in modes.split(',') {
                        let candidate = repack(&ordered, mode);
                        assert_eq!(
                            core_proto::circuit::compute_id(f, &candidate.raw),
                            ordered.id
                        );
                        let bytes = writer.to_bytes_lfc2(&candidate);
                        if component == 4 {
                            assert_eq!(bytes.len(), input.len());
                        }
                        let start = Instant::now();
                        let (decoded, tail) = reader.from_bytes(&bytes, false).unwrap();
                        let decode_ms = start.elapsed().as_secs_f64() * 1000.;
                        assert!(tail.is_empty());
                        assert_eq!(
                            core_proto::circuit::compute_id(f, &decoded.raw),
                            candidate.id
                        );
                        assert_eq!(writer.to_bytes_lfc2(&decoded), bytes);
                        for (a, b) in ordered.raw.layers.iter().zip(&decoded.raw.layers) {
                            assert_eq!(builder::records(a), builder::records(b));
                        }
                        let deltas = candidate
                            .raw
                            .layers
                            .iter()
                            .map(|l| l.deltas().len())
                            .sum::<usize>();
                        let segments = candidate
                            .raw
                            .layers
                            .iter()
                            .map(|l| l.delta_segments().len())
                            .sum::<usize>();
                        let tokens = candidate
                            .raw
                            .layers
                            .iter()
                            .map(|l| l.delta_tokens().len())
                            .sum::<usize>();
                        println!("ORDER_LFC2 dataset={name} wire={wire} components={component} window={window} order={order} traversal={traversal} segment={mode} raw={} z16={} z22={} deltas={deltas} segments={segments} tokens={tokens} build_ms={build_ms:.3} decode_ms={decode_ms:.3}",
                        bytes.len(),zstd::bulk::compress(&bytes,16).unwrap().len(),zstd::bulk::compress(&bytes,22).unwrap().len());
                        if let Ok(dir) = std::env::var("ORDER_SAVE_DIR") {
                            std::fs::create_dir_all(&dir).unwrap();
                            let prefix = if wire == "none" {
                                name.to_owned()
                            } else {
                                format!("{name}-wire_{wire}")
                            };
                            std::fs::write(format!("{dir}/{prefix}-b{component}-w{window}-o{order}-{traversal}-{mode}.lfc2"),bytes).unwrap();
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn boundary_segments_preserve_deltas_and_share_only_exact_runs() {
    use core_proto::TermDelta;
    let a = TermDelta {
        g: 0,
        h: [1, 2],
        k_index: 0,
    };
    let b = TermDelta {
        g: 1,
        h: [0, 1],
        k_index: 1,
    };
    let h0 = TermDelta {
        g: 3,
        h: [2, 1],
        k_index: 1,
    };
    let h1 = TermDelta {
        g: 7,
        h: [3, 4],
        k_index: 1,
    };
    let layer = Layer::<runtime_algebra::gf2_128::Gf2_128Field>::new_compressed(
        32,
        5,
        vec![vec![h0, a, b, a, b], vec![h1, a, b, a, b]],
        vec![0, 1],
    );
    let packed = boundary_segments(&layer, 2);
    let mut before = Vec::new();
    let mut after = Vec::new();
    layer.for_each_delta(|d| before.push(*d));
    packed.for_each_delta(|d| after.push(*d));
    assert_eq!(before, after);
    assert_eq!(packed.delta_segments().len(), 3);
    assert_eq!(packed.delta_tokens().len(), 6);
    assert_eq!(packed.num_terms(), 10);
    let short = reusable_interiors(&layer, 1);
    let mut actual = Vec::new();
    short.for_each_delta(|d| actual.push(*d));
    assert_eq!(actual, before);
    assert_eq!(
        short
            .delta_segments()
            .iter()
            .filter(|s| s.len() == 4)
            .count(),
        1
    );
    assert_eq!(
        short
            .delta_tokens()
            .iter()
            .filter(|&&t| short.delta_segments()[t as usize].len() == 4)
            .count(),
        2
    );
}

#[test]
fn repeated_interiors_are_shared_without_changing_boundary_deltas() {
    use core_proto::TermDelta;
    let body: Vec<_> = (0..40)
        .map(|i| TermDelta {
            g: i,
            h: [i + 1, 0],
            k_index: 0,
        })
        .collect();
    let run = |g| {
        std::iter::once(TermDelta {
            g,
            h: [0, 0],
            k_index: 0,
        })
        .chain(body.iter().copied())
        .collect()
    };
    let layer = Layer::<runtime_algebra::gf2_128::Gf2_128Field>::new_compressed(
        100,
        7,
        vec![run(91), run(93)],
        vec![0, 1],
    );
    let packed = reusable_interiors(&layer, 32);
    let mut before = Vec::new();
    let mut after = Vec::new();
    layer.for_each_delta(|d| before.push(*d));
    packed.for_each_delta(|d| after.push(*d));
    assert_eq!(before, after);
    assert_eq!(
        packed
            .delta_segments()
            .iter()
            .filter(|s| s.len() == 40)
            .count(),
        1
    );
    assert_eq!(
        packed
            .delta_tokens()
            .iter()
            .filter(|&&t| packed.delta_segments()[t as usize].len() == 40)
            .count(),
        2
    );
}

#[test]
fn clustered_dictionaries_preserve_traversal_and_reference_widths() {
    use core_proto::{writer::lfc2::uleb128_len_u32, TermDelta};
    let deltas = (0..260)
        .map(|i| TermDelta {
            g: 260 - i,
            h: [i, 0],
            k_index: 0,
        })
        .collect();
    let segments = (0..130).map(|i| vec![i, i + 130]).collect();
    let layer = Layer::<runtime_algebra::gf2_128::Gf2_128Field>::new(
        1024,
        10,
        deltas,
        segments,
        (0..130).collect(),
    );
    for both in [false, true] {
        let packed = clustered_dictionary(&layer, both);
        let mut before = Vec::new();
        let mut after = Vec::new();
        layer.for_each_delta(|d| before.push(*d));
        packed.for_each_delta(|d| after.push(*d));
        assert_eq!(before, after);
        for (&old, &new) in layer.delta_tokens().iter().zip(packed.delta_tokens()) {
            assert_eq!(uleb128_len_u32(old), uleb128_len_u32(new));
            for (&a, &b) in layer.delta_segments()[old as usize]
                .iter()
                .zip(&packed.delta_segments()[new as usize])
            {
                assert_eq!(uleb128_len_u32(a), uleb128_len_u32(b));
            }
        }
    }
}

#[test]
#[ignore = "offline template-order LFC2 sweep"]
fn layer_template_order_sweep() {
    let name = std::env::var("ORDER_DATASET").unwrap();
    match name.as_str() {
        "mdoc_hash1" | "mdoc_hash2" | "mdoc_hash3" | "mdoc_hash4" => run(
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
