// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Read-only ownership audit of the existing template-core LFC2 artifacts.
use super::*;

fn category(path: &str) -> u32 {
    if path.contains("shake256") || path.contains("keccak") {
        1
    } else if path.contains("inverse_ntt") {
        2
    } else if path.contains("ntt") {
        4
    } else if path.contains("sample_in_ball") {
        8
    } else if path.contains("hint") {
        16
    } else if path.contains("z_norm") {
        32
    } else if path.contains("w1_encode") {
        64
    } else {
        128
    }
}

#[derive(Clone, Copy, Default)]
struct Tags([u32; 3]);
impl Tags {
    fn join(&mut self, other: Self) {
        for (a, b) in self.0.iter_mut().zip(other.0) {
            *a |= b;
        }
    }
}

struct Bytes<'a> {
    input: &'a [u8],
    position: usize,
    buckets: [BTreeMap<u32, Vec<u8>>; 3],
    parts: BTreeMap<(&'static str, u32), usize>,
    ownership: BTreeMap<(u32, u32, u32), usize>,
    core_buckets: BTreeMap<u32, Vec<u8>>,
}
impl Bytes<'_> {
    fn take(&mut self, count: usize, tags: Tags, part: &'static str) {
        let bytes = &self.input[self.position..self.position + count];
        for (axis, &tag) in tags.0.iter().enumerate() {
            self.buckets[axis].entry(tag).or_default().extend(bytes);
        }
        *self.parts.entry((part, tags.0[0])).or_default() += count;
        *self
            .ownership
            .entry((tags.0[0], tags.0[1], tags.0[2]))
            .or_default() += count;
        let core_mask = match tags.0[0] {
            0 => 0,
            1..=3 => 1,
            4 => 4,
            _ => 5,
        };
        self.core_buckets
            .entry(core_mask)
            .or_default()
            .extend(bytes);
        self.position += count;
    }
    fn var(&mut self, expected: usize, tags: Tags, part: &'static str) {
        let mut actual = 0usize;
        let mut n = 0;
        loop {
            let byte = self.input[self.position + n];
            actual |= ((byte & 127) as usize) << (7 * n);
            n += 1;
            if byte < 128 {
                break;
            }
        }
        assert_eq!(actual, expected);
        self.take(n, tags, part);
    }
}

pub fn audit<F: AlgebraicField + SerializableField>(
    name: &str,
    f: &F,
    compiled: &Circuit<F>,
    symbols: &compile_compiler::CircuitDebugSymbols,
) {
    let reader = core_proto::reader::CircuitReader::new(f, FieldID::None);
    let input =
        std::fs::read(std::env::var("ORDER_AUDIT_SOURCE").unwrap_or_else(|_| {
            format!("target/traversal-circuits/{name}--kind_abs_lex0213_r5.lfc2")
        }))
        .unwrap();
    let (original, tail) = reader.from_bytes(&input, true).unwrap();
    assert!(tail.is_empty());
    assert_same_terms(f, compiled, &original);
    println!("AUDIT_SOURCE dataset={name} exact_wire_coordinate_term_match=true");
    let ts = terms(&original);
    let gr = graph(f, &original, &ts);
    let mut sources: Vec<Vec<u32>> = gr.counts.iter().map(|&n| vec![0; n]).collect();
    let mut paths = BTreeMap::new();
    for symbol in symbols.assertion_symbols() {
        let path = symbols.get_path(symbol.id).unwrap_or_default();
        let bit = category(&path);
        paths.entry(bit).or_insert(path);
        sources[ts.len() - symbol.wire.layer][symbol.wire.index] |= bit;
    }
    for (bit, path) in paths {
        println!("AUDIT_PATH bit={bit} example={path}");
    }
    // Attribute ancestors to their consuming assertions, without connecting
    // unrelated regions through constants or original inputs. Shared use is a
    // bit mask, not multiple independently counted source terms.
    for d in (0..ts.len()).rev() {
        for r in &ts[d] {
            let bit = sources[d + 1][r[0] as usize];
            if d > 0 {
                for h in [r[1], r[2]] {
                    if gr.constants[gr.offsets[d] + h as usize].is_none() {
                        sources[d][h as usize] |= bit;
                    }
                }
            }
        }
    }
    let (renamed, maps) = template_wires::renumber_with_maps(f, &original, "whole");
    let mut renamed_sources: Vec<Vec<u32>> = gr.counts.iter().map(|&n| vec![0; n]).collect();
    for d in 0..sources.len() {
        for (old, &new) in maps[d].iter().enumerate() {
            renamed_sources[d][new as usize] = sources[d][old];
        }
    }
    // Test one narrow explanation for failed exact matching: same local wiring,
    // differing only in coefficients. This does not change the extractor.
    let renamed_terms = terms(&renamed);
    let renamed_graph = graph(f, &renamed, &renamed_terms);
    let bs = blocks(&renamed_graph, &renamed_terms, false);
    let mut unmatched = BTreeMap::<(usize, u32, bool), usize>::new();
    let mut unmatched_shake = BTreeMap::<usize, usize>::new();
    for d in 0..ts.len() {
        let layer_blocks: Vec<_> = bs.iter().filter(|b| b.depth == d).collect();
        let mut exact = HashMap::<Vec<T>, usize>::new();
        let mut blind = HashMap::<Vec<T>, usize>::new();
        for b in &layer_blocks {
            let mut key = b.local.clone();
            key.sort_unstable();
            *exact.entry(key.clone()).or_default() += 1;
            for r in &mut key {
                r[3] = 0;
            }
            key.sort_unstable();
            *blind.entry(key).or_default() += 1;
        }
        for b in layer_blocks {
            let mut key = b.local.clone();
            key.sort_unstable();
            if exact[&key] > 1 {
                continue;
            }
            for r in &mut key {
                r[3] = 0;
            }
            key.sort_unstable();
            let coefficient_only = blind[&key] > 1;
            for r in &b.local {
                let source = renamed_sources[d + 1][b.outputs[r[0] as usize] as usize];
                *unmatched
                    .entry((d + 1, source, coefficient_only))
                    .or_default() += 1;
                if source == 1 {
                    *unmatched_shake.entry(b.component).or_default() += 1;
                }
            }
            if b.local.len() > 1000 {
                let mut source_terms = BTreeMap::<u32, usize>::new();
                for r in &b.local {
                    *source_terms
                        .entry(renamed_sources[d + 1][b.outputs[r[0] as usize] as usize])
                        .or_default() += 1;
                }
                println!("AUDIT_UNMATCHED_BLOCK dataset={name} depth={} outputs={} inputs={} terms={} sources={source_terms:?}",d+1,b.outputs.len(),b.inputs.len(),b.local.len());
            }
        }
    }
    for ((depth, source, coefficient_only), count) in unmatched {
        println!("AUDIT_UNMATCHED dataset={name} depth={depth} source={source} coefficient_only={coefficient_only} terms={count}");
    }
    let mut component_paths = BTreeMap::<usize, std::collections::BTreeSet<String>>::new();
    for symbol in symbols.assertion_symbols() {
        let d = ts.len() - symbol.wire.layer;
        let g = maps[d][symbol.wire.index] as usize;
        let component = renamed_graph.components[renamed_graph.offsets[d] + g];
        if unmatched_shake.contains_key(&component) {
            let path = symbols.get_path(symbol.id).unwrap_or_default();
            component_paths.entry(component).or_default().insert(
                path.split("/assert_eq_xor_state")
                    .next()
                    .unwrap()
                    .to_owned(),
            );
        }
    }
    for (component, count) in unmatched_shake {
        println!(
            "AUDIT_UNMATCHED_SHAKE dataset={name} component={component} terms={count} paths={:?}",
            component_paths.get(&component)
        );
    }
    let mut traces = Vec::new();
    let ordered = layer_template_control_traced(f, &renamed, 4, "shape_classes", Some(&mut traces));
    let stored = std::fs::read(std::env::var("ORDER_AUDIT_CANDIDATE").unwrap_or_else(|_| {
        format!(
            "target/template-core-lfc2/{name}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2"
        )
    }))
    .unwrap();
    let (candidate, tail) = reader.from_bytes(&stored, true).unwrap();
    assert!(tail.is_empty());
    assert_eq!(candidate.id, ordered.id);
    for (a, b) in candidate.raw.layers.iter().zip(&ordered.raw.layers) {
        assert_eq!(layer_templates::records(a), layer_templates::records(b));
    }
    println!("AUDIT_CANDIDATE dataset={name} exact_term_stream_and_id_match=true");
    let mut bytes = Bytes {
        input: &stored,
        position: 0,
        buckets: Default::default(),
        parts: BTreeMap::new(),
        ownership: BTreeMap::new(),
        core_buckets: BTreeMap::new(),
    };
    let meta = Tags::default();
    bytes.take(4, meta, "header");
    for val in [
        FieldID::None as usize,
        candidate.raw.noutput,
        1,
        candidate.raw.npublic_input,
        candidate.raw.subfield_boundary,
        candidate.raw.ninput,
        candidate.raw.layers.len(),
        candidate.raw.constants.len(),
    ] {
        bytes.var(val, meta, "header");
    }
    for k in &candidate.raw.constants {
        let expected = f.to_bytes(k);
        assert_eq!(
            &stored[bytes.position..bytes.position + expected.len()],
            &expected
        );
        bytes.take(expected.len(), meta, "constants");
    }
    let mut counts = BTreeMap::<(usize, u8, u32), usize>::new();
    for (li, (layer, trace)) in candidate.raw.layers.iter().zip(traces).enumerate() {
        let depth = candidate.raw.layers.len() - li;
        let records = layer_templates::records(layer);
        assert_eq!(trace.roles.len(), records.len());
        let tags: Vec<_> = records
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let source = renamed_sources[depth][r[0] as usize];
                *counts.entry((depth, trace.reasons[i], source)).or_default() += 1;
                Tags([trace.roles[i] as u32, 1 << trace.reasons[i], source])
            })
            .collect();
        let mut delta_tags = vec![Tags::default(); layer.deltas().len()];
        let mut segment_tags: Vec<Vec<Tags>> = layer
            .delta_segments()
            .iter()
            .map(|s| vec![Tags::default(); s.len()])
            .collect();
        let mut token_tags = Vec::new();
        let mut at = 0;
        for &token in layer.delta_tokens() {
            let mut token_tag = Tags::default();
            for (j, &delta) in layer.delta_segments()[token as usize].iter().enumerate() {
                let tag = tags[at];
                at += 1;
                token_tag.join(tag);
                delta_tags[delta as usize].join(tag);
                segment_tags[token as usize][j].join(tag);
            }
            token_tags.push(token_tag);
        }
        assert_eq!(at, records.len());
        for val in [layer.logw(), layer.nw(), layer.deltas().len()] {
            bytes.var(val, meta, "layer_header");
        }
        let before = bytes.position;
        for (d, tag) in layer.deltas().iter().zip(delta_tags) {
            for v in [d.g, d.h[0], d.h[1]] {
                bytes.var(
                    ((v << 1) ^ ((v as i32 >> 31) as u32)) as usize,
                    tag,
                    "delta",
                );
            }
            bytes.var(d.k_index as usize, tag, "delta");
        }
        let delta_bytes = bytes.position - before;
        bytes.var(layer.delta_segments().len(), meta, "layer_header");
        for (segment, tags) in layer.delta_segments().iter().zip(segment_tags) {
            let mut union = Tags::default();
            for &t in &tags {
                union.join(t);
            }
            bytes.var(segment.len(), union, "segment_length");
            for (&index, tag) in segment.iter().zip(tags) {
                bytes.var(index as usize, tag, "segment_entry");
            }
        }
        bytes.var(layer.delta_tokens().len(), meta, "layer_header");
        for (&token, tag) in layer.delta_tokens().iter().zip(token_tags) {
            bytes.var(token as usize, tag, "token");
        }
        println!(
            "AUDIT_LAYER dataset={name} depth={depth} terms={} delta_bytes={delta_bytes}",
            records.len()
        );
    }
    assert_eq!(&stored[bytes.position..], &candidate.id);
    bytes.take(32, meta, "id");
    assert_eq!(bytes.position, stored.len());
    for (axis, buckets) in bytes.buckets.iter().enumerate() {
        assert_eq!(buckets.values().map(Vec::len).sum::<usize>(), stored.len());
        for (&mask, stream) in buckets {
            let z22 = zstd::bulk::compress(stream, 22).unwrap().len();
            println!(
                "AUDIT_BYTES dataset={name} axis={axis} mask={mask} raw={} isolated_z22={z22}",
                stream.len()
            );
        }
    }
    for ((part, mask), count) in bytes.parts {
        println!("AUDIT_PART dataset={name} part={part} mask={mask} bytes={count}");
    }
    for (mask, stream) in bytes.core_buckets {
        println!(
            "AUDIT_CORE_BYTES dataset={name} mask={mask} raw={} isolated_z22={}",
            stream.len(),
            zstd::bulk::compress(&stream, 22).unwrap().len()
        );
    }
    for ((role, reason, source), count) in bytes.ownership {
        println!("AUDIT_OWNERSHIP dataset={name} role={role} reason={reason} source={source} bytes={count}");
    }
    for ((depth, reason, source), count) in counts {
        println!("AUDIT_TERMS dataset={name} depth={depth} reason={reason} source={source} terms={count}");
    }
    println!(
        "AUDIT_TOTAL dataset={name} raw={} z22={}",
        stored.len(),
        zstd::bulk::compress(&stored, 22).unwrap().len()
    );
}
