//! Offline, trusted-data experiment. No production scheduler or wire labels are changed.
//!
//! LCT0/LCT1 are experimental storage formats, not production readers: malformed
//! lengths/indices can panic or allocate excessively. The field is supplied by
//! the caller, as with the existing circuit readers. All templates, constants,
//! geometry, maps (including external ports), and the circuit ID are in the file.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Instant;

use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{
    circuit::{compute_id, Circuit, Layer, RawCircuit},
    FieldID, TermDelta,
};

#[path = "morton_key.rs"]
mod morton_key;

#[path = "wire_order.rs"]
mod wire_order;

#[path = "template_wires.rs"]
#[allow(dead_code)] // Standalone template-wire experiment, not every legacy harness.
pub mod template_wires;

#[path = "lex_order.rs"]
mod lex_order;

#[path = "bipartite.rs"]
mod bipartite;

#[path = "order_sweep.rs"]
mod order_sweep;

#[path = "dictionary_sweep.rs"]
mod dictionary_sweep;

#[path = "core_audit.rs"]
#[allow(dead_code)] // Used only by the dedicated offline ownership audit.
pub mod core_audit;
#[path = "layer_templates.rs"]
#[allow(dead_code)] // Also included by historical experiment harnesses.
pub mod layer_templates;
#[path = "lct_segment.rs"]
mod lct_segment;

/// Global-component template discovery used only to order ordinary LFC2 layers.
#[allow(dead_code)] // Invoked by the standalone layer_templates benchmark.
pub fn layer_template_control<F: AlgebraicField + SerializableField>(
    f: &F,
    c: &Circuit<F>,
    order: usize,
    traversal: &str,
) -> Circuit<F> {
    layer_template_control_traced(f, c, order, traversal, None)
}

/// Vanilla absolute Morton traversal, with original wire labels unchanged.
#[allow(dead_code)] // Used by the standalone ordering sweep.
pub fn absolute_morton_control<F: SerializableField>(f: &F, c: &Circuit<F>) -> Circuit<F> {
    let mut layers = terms(c);
    for layer in &mut layers {
        layer.sort_unstable_by(cmp);
    }
    rebuild(f, c, layers)
}

pub fn layer_template_control_traced<F: AlgebraicField + SerializableField>(
    f: &F,
    c: &Circuit<F>,
    order: usize,
    traversal: &str,
    mut traces: Option<&mut Vec<layer_templates::CoreTrace>>,
) -> Circuit<F> {
    use layer_templates::{ordered_layer, Group};
    let ts = terms(c);
    let gr = graph(f, c, &ts);
    let bs = blocks(&gr, &ts, false);
    let coefficients: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut layers = Vec::new();
    for (depth, layer) in c.raw.layers.iter().rev().enumerate() {
        let mut ids = HashMap::<Vec<T>, usize>::new();
        let mut groups: Vec<(Vec<T>, usize, Vec<Vec<u32>>)> = Vec::new();
        for b in bs.iter().filter(|b| b.depth == depth) {
            let mut local = b.local.clone();
            if order != 2 {
                local.sort_unstable();
            }
            layer_templates::sort_local(&mut local, order);
            if order == 4 || order == 6 || (10..=17).contains(&order) {
                let kind = |t: &T| {
                    let one = |h| {
                        gr.constants[gr.offsets[depth] + b.inputs[h as usize] as usize]
                            == gr.constants[0]
                    };
                    match (one(t[1]), one(t[2])) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        (false, false) if t[1] == t[2] => 2,
                        _ => 3,
                    }
                };
                local.sort_unstable_by(|a, b| {
                    kind(a).cmp(&kind(b)).then_with(|| {
                        if order == 6 {
                            cmp(a, b)
                        } else if (10..=17).contains(&order) {
                            let flags = order - 10;
                            let coord = |j: usize, flag: usize| {
                                if flags & flag != 0 {
                                    b[j].cmp(&a[j])
                                } else {
                                    a[j].cmp(&b[j])
                                }
                            };
                            coord(0, 1)
                                .then(coord(2, 2))
                                .then(coord(1, 4))
                                .then_with(|| {
                                    coefficients[a[3] as usize].cmp(&coefficients[b[3] as usize])
                                })
                        } else {
                            b[0].cmp(&a[0])
                                .then(b[2].cmp(&a[2]))
                                .then(a[1].cmp(&b[1]))
                                .then_with(|| {
                                    coefficients[a[3] as usize].cmp(&coefficients[b[3] as usize])
                                })
                        }
                    })
                });
            }
            let id = *ids.entry(local.clone()).or_insert_with(|| {
                let id = groups.len();
                groups.push((local, b.outputs.len(), Vec::new()));
                id
            });
            let mut map = b.outputs.clone();
            map.extend(&b.inputs);
            groups[id].2.push(map);
        }
        let groups = groups
            .into_iter()
            .map(|(program, ng, maps)| Group {
                program,
                ng,
                maps,
                affine: false,
                canonical_h: true,
            })
            .collect();
        let ones: Vec<_> = (0..layer.nw())
            .map(|h| gr.constants[gr.offsets[depth] + h] == gr.constants[0])
            .collect();
        if let Some(traces) = traces.as_deref_mut() {
            assert_eq!(traversal, "shape_classes");
            let mut trace = layer_templates::CoreTrace::default();
            layers.push(layer_templates::core_layer(
                layer.nw(),
                layer.logw(),
                groups,
                &ones,
                true,
                Some(&mut trace),
            ));
            traces.push(trace);
        } else {
            layers.push(ordered_layer(
                layer.nw(),
                layer.logw(),
                groups,
                &ones,
                traversal,
            ));
        }
    }
    layers.reverse();
    if let Some(traces) = traces {
        traces.reverse();
    }
    let raw = core_proto::circuit::RawCircuit {
        ninput: c.raw.ninput,
        npublic_input: c.raw.npublic_input,
        noutput: c.raw.noutput,
        logv: c.raw.logv,
        subfield_boundary: c.raw.subfield_boundary,
        constants: c.raw.constants.clone(),
        layers,
    };
    let id = core_proto::circuit::compute_id(f, &raw);
    Circuit { raw, id }
}

/// Offline lossless segmentation of LCT1, independent of runtime traversal.
#[allow(dead_code)]
pub fn analyze_lct_segmentation<F: AlgebraicField + SerializableField + Clone>(
    name: &str,
    f: &F,
    circuit: &Circuit<F>,
) {
    lct_segment::analyze(name, f, circuit);
}

#[allow(dead_code)]
pub fn kind_order<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
) -> Circuit<F> {
    order_sweep::kind_order(f, c)
}

#[allow(dead_code)]
pub fn fixed_input_wire_order<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    policy: &str,
) -> Circuit<F> {
    order_sweep::layer_wires::reorder(f, c, policy)
}

#[allow(dead_code)]
pub fn lane_order<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
) -> Circuit<F> {
    wire_order::lane_order(f, c)
}

// g, h0, h1, constant index. All equality/deduplication below is exact.
type T = [u32; 4];

/// Exact, traversal-independent check for offline imported candidate circuits.
pub fn assert_same_terms<F: SerializableField>(f: &F, a: &Circuit<F>, b: &Circuit<F>) {
    assert_eq!(
        (
            a.raw.ninput,
            a.raw.npublic_input,
            a.raw.noutput,
            a.raw.logv,
            a.raw.subfield_boundary
        ),
        (
            b.raw.ninput,
            b.raw.npublic_input,
            b.raw.noutput,
            b.raw.logv,
            b.raw.subfield_boundary
        )
    );
    assert_eq!(a.raw.layers.len(), b.raw.layers.len());
    for (x, y) in a.raw.layers.iter().zip(&b.raw.layers) {
        assert_eq!(
            (x.nw(), x.logw(), x.num_terms()),
            (y.nw(), y.logw(), y.num_terms())
        );
    }
    let canonical = |c: &Circuit<F>| {
        // segment_circuit frequency-orders the coefficient dictionary. Compare
        // semantic coefficient bytes, never incidental dictionary indices.
        let mut constants: Vec<_> = c
            .raw
            .constants
            .iter()
            .enumerate()
            .map(|(i, k)| (f.to_bytes(k), i))
            .collect();
        constants.sort_unstable();
        let mut ranks = vec![0; constants.len()];
        for (rank, (_, i)) in constants.iter().enumerate() {
            ranks[*i] = rank as u32;
        }
        let mut layers = terms(c);
        for l in &mut layers {
            for t in l.iter_mut() {
                t[3] = ranks[t[3] as usize];
            }
            l.sort_unstable();
        }
        (
            constants.into_iter().map(|(k, _)| k).collect::<Vec<_>>(),
            layers,
        )
    };
    assert!(
        canonical(a) == canonical(b),
        "coefficient values or term multiset changed"
    );
    assert_eq!(compute_id(f, &b.raw), b.id);
}

fn cmp(a: &T, b: &T) -> std::cmp::Ordering {
    cmp_coordinates(a, b).then(a[3].cmp(&b[3]))
}

fn cmp_coordinates(a: &T, b: &T) -> std::cmp::Ordering {
    let x = a[1] ^ b[1];
    let y = a[2] ^ b[2];
    let order = if y.leading_zeros() <= x.leading_zeros() {
        a[2].cmp(&b[2]).then(a[1].cmp(&b[1]))
    } else {
        a[1].cmp(&b[1]).then(a[2].cmp(&b[2]))
    };
    order.then(a[0].cmp(&b[0]))
}

fn root(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let x = root(parent, a);
    let y = root(parent, b);
    parent[x.max(y)] = x.min(y);
}

fn terms<F: SerializableField>(c: &Circuit<F>) -> Vec<Vec<T>> {
    c.raw
        .layers
        .iter()
        .rev()
        .map(|layer| {
            let mut previous = [0u32; 3];
            let mut result = Vec::with_capacity(layer.num_terms());
            layer.for_each_delta(|delta| {
                previous[0] = previous[0].wrapping_add(delta.g);
                previous[1] = previous[1].wrapping_add(delta.h[0]);
                previous[2] = previous[2].wrapping_add(delta.h[1]);
                result.push([previous[0], previous[1], previous[2], delta.k_index]);
            });
            result
        })
        .collect()
}

struct Graph {
    offsets: Vec<usize>,
    counts: Vec<usize>,
    components: Vec<usize>,
    // None = nonconstant. Some = index of actual constant value in an exact table.
    constants: Vec<Option<u32>>,
}

fn graph<F: AlgebraicField + SerializableField>(f: &F, c: &Circuit<F>, ts: &[Vec<T>]) -> Graph {
    let mut counts = vec![c.raw.ninput];
    counts.extend(
        ts.iter()
            .map(|layer| 1 + layer.iter().map(|t| t[0] as usize).max().unwrap()),
    );
    let mut offsets = vec![0];
    for n in &counts {
        offsets.push(offsets.last().unwrap() + n);
    }
    let total = *offsets.last().unwrap();
    let mut parent: Vec<_> = (0..total).collect();
    let mut known: Vec<Option<F::E>> = vec![None; total];
    known[0] = Some(f.one());
    for (d, layer) in ts.iter().enumerate() {
        let mut values = vec![f.zero(); counts[d + 1]];
        let mut is_constant = vec![true; counts[d + 1]];
        for t in layer {
            let k = &c.raw.constants[t[3] as usize];
            let a = &known[offsets[d] + t[1] as usize];
            let b = &known[offsets[d] + t[2] as usize];
            // Zero-coefficient terms are assertion markers, not ordinary zero gates.
            if let (Some(a), Some(b)) = (a, b) {
                if !f.is_zero(k) {
                    f.add(&mut values[t[0] as usize], &f.mulf(k, &f.mulf(a, b)));
                } else {
                    is_constant[t[0] as usize] = false;
                }
            } else {
                is_constant[t[0] as usize] = false;
            }
        }
        for (g, (value, yes)) in values.into_iter().zip(is_constant).enumerate() {
            if yes {
                known[offsets[d + 1] + g] = Some(value);
            }
        }
        for t in layer {
            let g = offsets[d + 1] + t[0] as usize;
            if known[g].is_none() && d > 0 {
                for h in [t[1], t[2]] {
                    let child = offsets[d] + h as usize;
                    if known[child].is_none() {
                        union(&mut parent, g, child);
                    }
                }
            }
        }
    }
    let components = (0..total).map(|i| root(&mut parent, i)).collect();
    let mut value_table = BTreeMap::new();
    for value in known.iter().flatten() {
        value_table.insert(f.to_bytes(value), 0);
    }
    for (i, index) in value_table.values_mut().enumerate() {
        *index = i as u32;
    }
    let constants = known
        .into_iter()
        .map(|v| v.map(|x| value_table[&f.to_bytes(&x)]))
        .collect();
    Graph {
        offsets,
        counts,
        components,
        constants,
    }
}

#[derive(Clone)]
struct Block {
    component: usize,
    depth: usize,
    outputs: Vec<u32>,
    inputs: Vec<u32>,
    // External ports precede internal wires; tags distinguish input ports and constant values.
    ports: Vec<u32>,
    absolute_local: Vec<T>,
    local: Vec<T>,
}

fn blocks(graph: &Graph, ts: &[Vec<T>], structural: bool) -> Vec<Block> {
    let mut result = Vec::new();
    let mut rank = vec![0u32; graph.components.len()];
    for (d, layer) in ts.iter().enumerate() {
        let mut groups = BTreeMap::<usize, Vec<T>>::new();
        for &t in layer {
            groups
                .entry(graph.components[graph.offsets[d + 1] + t[0] as usize])
                .or_default()
                .push(t);
        }
        for (component, group) in groups {
            let mut outputs: Vec<_> = group.iter().map(|t| t[0]).collect();
            outputs.sort_unstable();
            outputs.dedup();
            let mut inputs: Vec<_> = group.iter().flat_map(|t| [t[1], t[2]]).collect();
            inputs.sort_unstable();
            inputs.dedup();
            inputs.sort_by_key(|&h| {
                let index = graph.offsets[d] + h as usize;
                if let Some(k) = graph.constants[index] {
                    (0, k, h)
                } else if d == 0 {
                    (1, h, h)
                } else {
                    assert_eq!(graph.components[index], component);
                    (2, if structural { rank[index] } else { h }, h)
                }
            });
            let ports: Vec<_> = inputs
                .iter()
                .filter_map(|&h| {
                    let index = graph.offsets[d] + h as usize;
                    graph.constants[index]
                        .map(|k| 2 + k)
                        .or_else(|| (d == 0).then_some(1))
                })
                .collect();
            let hmap: HashMap<_, _> = inputs
                .iter()
                .enumerate()
                .map(|(i, &h)| (h, i as u32))
                .collect();
            if structural {
                let mut descriptors = HashMap::<u32, Vec<[u32; 3]>>::new();
                for t in &group {
                    let a = hmap[&t[1]];
                    let b = hmap[&t[2]];
                    descriptors
                        .entry(t[0])
                        .or_default()
                        .push([a.min(b), a.max(b), t[3]]);
                }
                for terms in descriptors.values_mut() {
                    terms.sort_unstable();
                }
                outputs.sort_by(|a, b| descriptors[a].cmp(&descriptors[b]).then(a.cmp(b)));
                // Duplicate expressions would leave ambiguity in structural labeling.
                assert!(outputs
                    .windows(2)
                    .all(|p| descriptors[&p[0]] != descriptors[&p[1]]));
            }
            let gmap: HashMap<_, _> = outputs
                .iter()
                .enumerate()
                .map(|(i, &g)| (g, i as u32))
                .collect();
            for (&g, &r) in &gmap {
                rank[graph.offsets[d + 1] + g as usize] = r;
            }
            let absolute_local: Vec<_> = group
                .iter()
                .map(|t| {
                    let a = hmap[&t[1]];
                    let b = hmap[&t[2]];
                    [gmap[&t[0]], a.min(b), a.max(b), t[3]]
                })
                .collect();
            let mut local = absolute_local.clone();
            local.sort_unstable_by(cmp);
            result.push(Block {
                component,
                depth: d,
                outputs,
                inputs,
                ports,
                absolute_local,
                local,
            });
        }
    }
    result
}

fn deltas(ts: &[T]) -> Vec<T> {
    let mut previous = [0u32; 3];
    ts.iter()
        .map(|t| {
            let result = [
                t[0].wrapping_sub(previous[0]),
                t[1].wrapping_sub(previous[1]),
                t[2].wrapping_sub(previous[2]),
                t[3],
            ];
            previous.copy_from_slice(&t[..3]);
            result
        })
        .collect()
}

// True offset removal, WITHOUT packing holes in internal wire coordinates.
// Shared inputs/constants are named ports, not translated component members.
fn offset_sequences(blocks: &[Block]) -> Vec<(Vec<T>, Vec<T>, usize)> {
    let bases: HashMap<_, _> = blocks
        .iter()
        .map(|b| ((b.component, b.depth + 1), *b.outputs.iter().min().unwrap()))
        .collect();
    blocks
        .iter()
        .map(|b| {
            let gb = bases[&(b.component, b.depth + 1)];
            let hb = bases.get(&(b.component, b.depth)).copied().unwrap_or(0);
            let h = |r: u32| {
                if (r as usize) < b.ports.len() {
                    r
                } else {
                    b.ports.len() as u32 + b.inputs[r as usize] - hb
                }
            };
            let original: Vec<_> = b
                .absolute_local
                .iter()
                .map(|t| {
                    let a = h(t[1]);
                    let c = h(t[2]);
                    [b.outputs[t[0] as usize] - gb, a.min(c), a.max(c), t[3]]
                })
                .collect();
            let mut local = original.clone();
            local.sort_unstable_by(cmp);
            (original, local, b.ports.len())
        })
        .collect()
}

fn sequence_stats(label: &str, sequences: impl Iterator<Item = Vec<T>>) {
    let mut unique = HashSet::new();
    let mut chunks = HashMap::<Vec<T>, usize>::new();
    let mut total = 0;
    for sequence in sequences {
        total += sequence.len();
        unique.extend(sequence.iter().copied());
        for chunk in sequence.chunks_exact(32) {
            *chunks.entry(chunk.to_vec()).or_default() += 1;
        }
    }
    let repeated: usize = chunks.values().filter(|&&n| n > 1).sum();
    let all: usize = chunks.values().sum();
    let triples: HashSet<_> = unique.iter().map(|t| [t[0], t[1], t[2]]).collect();
    println!(
        "SEQUENCES {label}: terms={total} distinct_deltas={} chunks32={} unique_chunks32={} repeated_chunk_occurrences={repeated} distinct_coordinate_triples={}",
        unique.len(),
        all,
        chunks.len(),
        triples.len()
    );
}

fn signature(block: &Block) -> Vec<u32> {
    let mut key = vec![
        block.depth as u32,
        block.outputs.len() as u32,
        block.inputs.len() as u32,
        block.ports.len() as u32,
    ];
    key.extend(&block.ports);
    // Explicit previous-layer ranks are supplied by the whole-component verifier below.
    key.extend(block.local.iter().flatten());
    key
}

fn correspondence(
    label: &str,
    blocks: &[Block],
    graph: &Graph,
    symbols: &compile_compiler::CircuitDebugSymbols,
) {
    let mut by_component = BTreeMap::<usize, Vec<&Block>>::new();
    for block in blocks {
        by_component.entry(block.component).or_default().push(block);
    }
    let mut families = HashMap::<Vec<u32>, Vec<usize>>::new();
    let mut locations = HashMap::<usize, String>::new();
    for symbol in symbols.assertion_symbols() {
        let depth = graph.counts.len() - 1 - symbol.wire.layer;
        let component = graph.components[graph.offsets[depth] + symbol.wire.index];
        if let Some(path) = symbols.get_path(symbol.id) {
            locations.entry(component).or_insert(path);
        }
    }
    for (&component, bs) in &by_component {
        let size: usize = bs.iter().map(|b| b.outputs.len()).sum();
        if size < 1000 {
            continue;
        }
        let mut wire_ranks = HashMap::new();
        for b in bs {
            for (i, &g) in b.outputs.iter().enumerate() {
                wire_ranks.insert((b.depth + 1, g), i as u32);
            }
        }
        let mut key = Vec::new();
        for b in bs {
            let s = signature(b);
            key.push(s.len() as u32);
            key.extend(s);
            // Input mapping to previous local outputs makes this a full DAG correspondence,
            // rather than independent per-layer coincidences.
            for &h in b.inputs.iter().skip(b.ports.len()) {
                key.push(wire_ranks[&(b.depth, h)]);
            }
        }
        families.entry(key).or_default().push(component);
    }
    let mut repeated: Vec<_> = families.values().filter(|v| v.len() > 1).collect();
    repeated.sort_by_key(|v| (std::cmp::Reverse(v.len()), v[0]));
    println!(
        "CORRESPONDENCE {label}: repeated_whole_component_families={}",
        repeated.len()
    );
    for family in repeated.iter().take(4) {
        let a = family[0];
        let b = family[1];
        let aa = &by_component[&a];
        let bb = &by_component[&b];
        let wires: usize = aa.iter().map(|x| x.outputs.len()).sum();
        let terms: usize = aa.iter().map(|x| x.local.len()).sum();
        let equal_absolute_sequences = aa
            .iter()
            .zip(bb)
            .filter(|(x, y)| x.absolute_local == y.absolute_local)
            .count();
        let different_absolute_positions: usize = aa
            .iter()
            .zip(bb)
            .map(|(x, y)| {
                x.absolute_local
                    .iter()
                    .zip(&y.absolute_local)
                    .filter(|(a, b)| a != b)
                    .count()
            })
            .sum();
        println!(
            "PAIR {label}: components={a},{b} family={} wires={wires} terms={terms} exact_local_DAG=true same_normalized_absolute_layers={}/{} differing_sequence_positions={different_absolute_positions} paths={:?} / {:?}",
            family.len(),
            equal_absolute_sequences,
            aa.len(),
            locations.get(&a),
            locations.get(&b)
        );
        let mut translated_layers = 0;
        let mut translated_interior_mismatch_layers = 0;
        let mut interior_mismatches = 0;
        for (x, y) in aa.iter().zip(bb) {
            let uniform = |a: &[u32], b: &[u32]| {
                !a.is_empty()
                    && a.iter()
                        .zip(b)
                        .all(|(&g, &h)| h.wrapping_sub(g) == b[0].wrapping_sub(a[0]))
            };
            let translated = uniform(&x.outputs, &y.outputs)
                && uniform(&x.inputs[x.ports.len()..], &y.inputs[y.ports.len()..]);
            let interior = |b: &Block| {
                b.absolute_local
                    .iter()
                    .filter(|t| t[1] as usize >= b.ports.len() && t[2] as usize >= b.ports.len())
                    .copied()
                    .collect::<Vec<_>>()
            };
            let xx = interior(x);
            let yy = interior(y);
            let mismatches = xx.iter().zip(&yy).filter(|(a, b)| a != b).count();
            interior_mismatches += mismatches;
            if translated {
                translated_layers += 1;
            }
            if translated && mismatches > 0 {
                translated_interior_mismatch_layers += 1;
                if translated_interior_mismatch_layers == 1 {
                    let i = xx.iter().zip(&yy).position(|(a, b)| a != b).unwrap();
                    let absolute = |b: &Block, t: &T| {
                        [
                            b.outputs[t[0] as usize],
                            b.inputs[t[1] as usize],
                            b.inputs[t[2] as usize],
                            t[3],
                        ]
                    };
                    println!(
                        "TRANSLATION_WITNESS {label}: depth={} dg={} dh={} first_interior_mismatch={i} local_a={:?} local_b={:?} left_a={:?} left_b={:?} right_a={:?} right_b={:?}",
                        x.depth + 1,
                        y.outputs[0] as i64 - x.outputs[0] as i64,
                        y.inputs[y.ports.len()] as i64 - x.inputs[x.ports.len()] as i64,
                        xx[i],
                        yy[i],
                        absolute(x, &xx[i]),
                        absolute(x, &yy[i]),
                        absolute(y, &xx[i]),
                        absolute(y, &yy[i])
                    );
                }
            }
        }
        println!(
            "PAIR_CAUSES {label}: uniform_output_and_internal_input_translation_layers={translated_layers}/{} translated_interior_mismatch_layers={translated_interior_mismatch_layers} interior_sequence_mismatches={interior_mismatches}",
            aa.len()
        );
        for (x, y) in aa
            .iter()
            .zip(bb)
            .filter(|(x, y)| x.absolute_local != y.absolute_local)
            .take(2)
        {
            let first = x
                .absolute_local
                .iter()
                .zip(&y.absolute_local)
                .position(|(a, b)| a != b)
                .unwrap();
            println!(
                "PAIR_LAYER depth={} first_mismatch={first} left={:?} right={:?} output_bases={},{} shared_ports={} input_bases={:?},{:?}",
                x.depth + 1,
                x.absolute_local[first],
                y.absolute_local[first],
                x.outputs[0],
                y.outputs[0],
                x.ports.len(),
                x.inputs.get(x.ports.len()),
                y.inputs.get(y.ports.len())
            );
        }
    }
}

fn put(out: &mut Vec<u8>, mut n: u32) {
    while n >= 128 {
        out.push((n as u8) | 128);
        n >>= 7;
    }
    out.push(n as u8);
}
fn get(input: &mut &[u8]) -> u32 {
    let mut value = 0;
    for shift in (0..35).step_by(7) {
        let b = input[0];
        *input = &input[1..];
        value |= u32::from(b & 127) << shift;
        if b < 128 {
            return value;
        }
    }
    panic!("invalid varint");
}
fn zig(n: u32) -> u32 {
    (n << 1) ^ ((n as i32 >> 31) as u32)
}
fn unzig(n: u32) -> u32 {
    (n >> 1) ^ 0u32.wrapping_sub(n & 1)
}

// Maps are encoded as runs of consecutive absolute wires. Arbitrary permutations are legal;
// singleton runs cover them and all their bytes are included in measurements.
fn put_map(out: &mut Vec<u8>, map: &[u32]) {
    put(out, map.len() as u32);
    let mut i = 0;
    let mut previous = 0u32;
    while i < map.len() {
        let mut end = i + 1;
        while end < map.len() && map[end] == map[end - 1] + 1 {
            end += 1;
        }
        put(out, zig(map[i].wrapping_sub(previous)));
        put(out, (end - i) as u32);
        previous = map[end - 1];
        i = end;
    }
}
fn get_map(input: &mut &[u8]) -> Vec<u32> {
    let count = get(input) as usize;
    let mut out = Vec::with_capacity(count);
    let mut previous = 0u32;
    while out.len() < count {
        let start = previous.wrapping_add(unzig(get(input)));
        let len = get(input);
        out.extend(start..start + len);
        previous = start + len - 1;
    }
    assert_eq!(out.len(), count);
    out
}

fn header<F: SerializableField>(f: &F, c: &Circuit<F>) -> Vec<u8> {
    let mut out = b"LCT0".to_vec();
    for n in [
        c.raw.ninput,
        c.raw.npublic_input,
        c.raw.noutput,
        c.raw.logv,
        c.raw.subfield_boundary,
        c.raw.layers.len(),
        c.raw.constants.len(),
    ] {
        put(&mut out, n as u32);
    }
    for k in &c.raw.constants {
        out.extend(f.to_bytes(k));
    }
    out.extend(c.id);
    for layer in c.raw.layers.iter().rev() {
        put(&mut out, layer.nw() as u32);
        put(&mut out, layer.logw() as u32);
    }
    out
}

fn encode<F: SerializableField>(f: &F, c: &Circuit<F>, blocks: &[Block]) -> Vec<u8> {
    let mut out = header(f, c);
    let header = out.len();
    let mut templates = Vec::new();
    let mut ids = HashMap::<&[T], u32>::new();
    for b in blocks {
        if !ids.contains_key(b.local.as_slice()) {
            ids.insert(&b.local, templates.len() as u32);
            templates.push(&b.local);
        }
    }
    put(&mut out, templates.len() as u32);
    for ts in &templates {
        put(&mut out, ts.len() as u32);
        for d in deltas(ts) {
            for n in &d[..3] {
                put(&mut out, zig(*n));
            }
            put(&mut out, d[3]);
        }
    }
    let template_bytes = out.len() - header;
    put(&mut out, blocks.len() as u32);
    let mut mapping_bytes = 0;
    let mut shared_ports = 0;
    for b in blocks {
        put(&mut out, b.depth as u32);
        put(&mut out, ids[b.local.as_slice()]);
        let before = out.len();
        put_map(&mut out, &b.outputs);
        put_map(&mut out, &b.inputs);
        mapping_bytes += out.len() - before;
        shared_ports += b.ports.len();
    }
    println!(
        "ENCODING header={header} templates={} template_bytes={template_bytes} instances={} mappings={mapping_bytes} shared_port_entries={shared_ports} total={}",
        templates.len(),
        blocks.len(),
        out.len()
    );
    out
}

// One fixed, columnar rule: group instances by their exact local template, order
// by depth then output coordinates, and RLE the coordinate-wise map differences.
// Unlike LCT0, this retains regularity BETWEEN instances (important for mdoc).
fn put_map_difference(out: &mut Vec<u8>, map: &[u32], previous: &mut Vec<u32>) {
    if previous.is_empty() {
        previous.resize(map.len(), 0);
    }
    assert_eq!(previous.len(), map.len());
    let differences: Vec<_> = map
        .iter()
        .zip(previous.iter())
        .map(|(&a, &b)| a.wrapping_sub(b))
        .collect();
    let mut i = 0;
    while i < differences.len() {
        let mut end = i + 1;
        while end < differences.len() && differences[end] == differences[i] {
            end += 1;
        }
        put(out, (end - i) as u32);
        put(out, zig(differences[i]));
        i = end;
    }
    previous.copy_from_slice(map);
}

fn get_map_difference(input: &mut &[u8], previous: &mut [u32]) {
    let mut i = 0;
    while i < previous.len() {
        let count = get(input) as usize;
        let difference = unzig(get(input));
        for p in &mut previous[i..i + count] {
            *p = p.wrapping_add(difference);
        }
        i += count;
    }
}

fn encode_grouped<F: SerializableField>(f: &F, c: &Circuit<F>, blocks: &[Block]) -> Vec<u8> {
    let mut out = header(f, c);
    out[3] = b'1';
    let header_bytes = out.len();
    let mut groups = Vec::<Vec<&Block>>::new();
    let mut ids = HashMap::<&[T], usize>::new();
    for b in blocks {
        let id = *ids.entry(&b.local).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[id].push(b);
    }
    put(&mut out, groups.len() as u32);
    let mut template_bytes = 0;
    let mut mapping_bytes = 0;
    let mut shared_ports = 0;
    for group in &mut groups {
        group.sort_by(|a, b| a.depth.cmp(&b.depth).then(a.outputs.cmp(&b.outputs)));
        let b = group[0];
        let start = out.len();
        put(&mut out, b.local.len() as u32);
        put(&mut out, b.outputs.len() as u32);
        put(&mut out, b.inputs.len() as u32);
        for d in deltas(&b.local) {
            for n in &d[..3] {
                put(&mut out, zig(*n));
            }
            put(&mut out, d[3]);
        }
        template_bytes += out.len() - start;
        put(&mut out, group.len() as u32);
        let mut gs = Vec::new();
        let mut hs = Vec::new();
        let mut depth = 0u32;
        for (index, b) in group.iter().enumerate() {
            put(&mut out, b.depth as u32 - depth);
            depth = b.depth as u32;
            let start = out.len();
            if index == 0 {
                put_map(&mut out, &b.outputs);
                put_map(&mut out, &b.inputs);
                gs = b.outputs.clone();
                hs = b.inputs.clone();
            } else {
                put_map_difference(&mut out, &b.outputs, &mut gs);
                put_map_difference(&mut out, &b.inputs, &mut hs);
            }
            mapping_bytes += out.len() - start;
            shared_ports += b.ports.len();
        }
    }
    println!(
        "ENCODING_GROUPED header={header_bytes} templates={} template_bytes={template_bytes} instances={} mappings={mapping_bytes} shared_port_entries={shared_ports} total={}",
        groups.len(),
        blocks.len(),
        out.len()
    );
    out
}

fn rebuild<F: SerializableField>(f: &F, c: &Circuit<F>, layers: Vec<Vec<T>>) -> Circuit<F> {
    let layers: Vec<_> = layers
        .into_iter()
        .zip(c.raw.layers.iter().rev())
        .map(|(ts, old)| {
            let ds = deltas(&ts)
                .into_iter()
                .map(|d| TermDelta {
                    g: d[0],
                    h: [d[1], d[2]],
                    k_index: d[3],
                })
                .collect();
            Layer::new_compressed(old.nw(), old.logw(), vec![ds], vec![0])
        })
        .rev()
        .collect();
    let raw = RawCircuit {
        ninput: c.raw.ninput,
        npublic_input: c.raw.npublic_input,
        noutput: c.raw.noutput,
        logv: c.raw.logv,
        subfield_boundary: c.raw.subfield_boundary,
        constants: c.raw.constants.clone(),
        layers,
    };
    let id = compute_id(f, &raw);
    Circuit { raw, id }
}

fn decode<F: SerializableField>(f: &F, bytes: &[u8]) -> Circuit<F> {
    assert!(&bytes[..4] == b"LCT0" || &bytes[..4] == b"LCT1");
    let grouped = bytes[3] == b'1';
    let mut input = &bytes[4..];
    let ninput = get(&mut input) as usize;
    let npublic_input = get(&mut input) as usize;
    let noutput = get(&mut input) as usize;
    let logv = get(&mut input) as usize;
    let subfield_boundary = get(&mut input) as usize;
    let nl = get(&mut input) as usize;
    let nk = get(&mut input) as usize;
    let mut constants = Vec::new();
    let width = f.serialized_size_bytes();
    for _ in 0..nk {
        constants.push(f.bytes_to_element(&input[..width]).ok().unwrap());
        input = &input[width..];
    }
    let id: [u8; 32] = input[..32].try_into().unwrap();
    input = &input[32..];
    let geometry: Vec<_> = (0..nl)
        .map(|_| (get(&mut input) as usize, get(&mut input) as usize))
        .collect();
    let nt = get(&mut input);
    let mut templates = Vec::new();
    let mut layers = vec![Vec::<T>::new(); nl];
    let expand = |layer: &mut Vec<T>, ts: &[T], gs: &[u32], hs: &[u32]| {
        for t in ts {
            let a = hs[t[1] as usize];
            let b = hs[t[2] as usize];
            layer.push([gs[t[0] as usize], a.min(b), a.max(b), t[3]]);
        }
    };
    for _ in 0..nt {
        let count = get(&mut input);
        let mut gs = Vec::new();
        let mut hs = Vec::new();
        if grouped {
            gs.resize(get(&mut input) as usize, 0);
            hs.resize(get(&mut input) as usize, 0);
        }
        let mut ts = Vec::new();
        let mut previous = [0u32; 3];
        for _ in 0..count {
            for p in &mut previous {
                *p = p.wrapping_add(unzig(get(&mut input)));
            }
            let k = get(&mut input);
            ts.push([previous[0], previous[1], previous[2], k]);
        }
        if grouped {
            let count = get(&mut input);
            let mut d = 0;
            for index in 0..count {
                d += get(&mut input) as usize;
                if index == 0 {
                    let ng = gs.len();
                    let nh = hs.len();
                    gs = get_map(&mut input);
                    hs = get_map(&mut input);
                    assert_eq!(gs.len(), ng);
                    assert_eq!(hs.len(), nh);
                } else {
                    get_map_difference(&mut input, &mut gs);
                    get_map_difference(&mut input, &mut hs);
                }
                expand(&mut layers[d], &ts, &gs, &hs);
            }
        } else {
            templates.push(ts);
        }
    }
    if !grouped {
        let nb = get(&mut input);
        for _ in 0..nb {
            let d = get(&mut input) as usize;
            let tid = get(&mut input) as usize;
            let gs = get_map(&mut input);
            let hs = get_map(&mut input);
            expand(&mut layers[d], &templates[tid], &gs, &hs);
        }
    }
    assert!(input.is_empty());
    let sort_start = Instant::now();
    for layer in &mut layers {
        layer.sort_unstable_by(|a, b| {
            cmp_coordinates(a, b).then_with(|| {
                f.to_bytes(&constants[a[3] as usize])
                    .cmp(&f.to_bytes(&constants[b[3] as usize]))
            })
        });
    }
    println!(
        "DECODE canonical_sort_ms={:.3}",
        sort_start.elapsed().as_secs_f64() * 1000.
    );
    let layers = layers
        .into_iter()
        .zip(geometry)
        .map(|(ts, (nw, logw))| {
            let ds = deltas(&ts)
                .into_iter()
                .map(|d| TermDelta {
                    g: d[0],
                    h: [d[1], d[2]],
                    k_index: d[3],
                })
                .collect();
            Layer::new_compressed(nw, logw, vec![ds], vec![0])
        })
        .rev()
        .collect();
    let raw = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv,
        subfield_boundary,
        constants,
        layers,
    };
    assert_eq!(compute_id(f, &raw), id);
    Circuit { raw, id }
}

fn sizes(label: &str, bytes: &[u8]) {
    let z16 = zstd::bulk::compress(bytes, 16).unwrap();
    let z22 = zstd::bulk::compress(bytes, 22).unwrap();
    println!(
        "SIZE {label}: raw={} zstd16={} zstd22={}",
        bytes.len(),
        z16.len(),
        z22.len()
    );
}

pub fn analyze<F: AlgebraicField + SerializableField + Clone>(
    name: &str,
    f: &F,
    c: &Circuit<F>,
    symbols: &compile_compiler::CircuitDebugSymbols,
    field_id: FieldID,
) {
    println!("ANALYZE {name} id={:02x?}", c.id);
    if std::env::var_os("MORTON_DICTIONARY_SWEEP").is_some() {
        dictionary_sweep::analyze(f, c, field_id);
        return;
    }
    if std::env::var_os("MORTON_ORDER_SWEEP").is_some() {
        order_sweep::analyze(f, c, field_id);
        return;
    }
    if std::env::var_os("MORTON_BIPARTITE_ONLY").is_some() {
        bipartite::analyze(f, c, field_id);
        return;
    }
    if std::env::var_os("MORTON_LEX_ORDER_ONLY").is_some() {
        lex_order::analyze(f, c, field_id);
        return;
    }
    if std::env::var_os("MORTON_LANE_ORDER_ONLY").is_some() {
        wire_order::analyze(f, c, field_id);
        return;
    }
    if std::env::var_os("MORTON_KEY_DELTAS_ONLY").is_some() {
        morton_key::analyze(f, c, field_id);
        return;
    }
    let ts = terms(c);
    let graph = graph(f, c, &ts);
    if std::env::var_os("MORTON_DECODE_ONLY").is_some() {
        let writer = core_proto::writer::CircuitWriter::new(f, field_id);
        let original = writer.to_bytes_lfc1(c);
        let bs = blocks(&graph, &ts, false);
        let formats = [
            ("LFC1", original.clone()),
            ("LFC2", writer.to_bytes_lfc2(c)),
            ("LCT1", encode_grouped(f, c, &bs)),
        ];
        for (label, bytes) in formats {
            let packed = zstd::bulk::compress(&bytes, 16).unwrap();
            let mut times = Vec::new();
            for _ in 0..3 {
                let start = Instant::now();
                let unpacked = zstd::bulk::decompress(&packed, bytes.len()).unwrap();
                let recovered = match label {
                    "LFC1" => {
                        core_proto::reader::CircuitReader::new(f, field_id)
                            .from_bytes_lfc1(&unpacked, true)
                            .unwrap()
                            .0
                    }
                    "LFC2" => {
                        core_proto::reader::CircuitReader::new(f, field_id)
                            .from_bytes_lfc2(&unpacked, true)
                            .unwrap()
                            .0
                    }
                    _ => decode(f, &unpacked),
                };
                times.push(start.elapsed().as_secs_f64() * 1000.);
                assert_eq!(writer.to_bytes_lfc1(&recovered), original);
            }
            times.sort_by(f64::total_cmp);
            println!(
                "DECODE_BENCH {label}: zstd16_plus_decode_hash_median_ms={:.3} runs_ms={times:?} exact_lfc1=true",
                times[1]
            );
        }
        return;
    }
    let mut cs = HashMap::<usize, usize>::new();
    for d in 1..graph.counts.len() {
        for g in 0..graph.counts[d] {
            *cs.entry(graph.components[graph.offsets[d] + g])
                .or_default() += 1;
        }
    }
    let mut big: Vec<_> = cs.values().copied().collect();
    big.sort_unstable_by(|a, b| b.cmp(a));
    println!(
        "GRAPH components={} largest={:?} constants={} inputs={}",
        cs.len(),
        &big[..big.len().min(40)],
        graph.constants.iter().filter(|v| v.is_some()).count(),
        graph.counts[0]
    );
    sequence_stats("absolute", ts.iter().map(|t| deltas(t)));
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let original = writer.to_bytes_lfc1(c);
    let diagnostics_only = std::env::var_os("MORTON_DIAGNOSTICS_ONLY").is_some();
    if !diagnostics_only {
        sizes("canonical_lfc1", &original);
        let lfc2 = writer.to_bytes_lfc2(c);
        sizes("canonical_lfc2", &lfc2);
        let segmented = compile_compiler::segment_circuit(f, c);
        sizes(
            "canonical_lfc2_resegment",
            &writer.to_bytes_lfc2(&segmented),
        );
        drop(segmented);
        let start = Instant::now();
        let _ = core_proto::reader::CircuitReader::new(f, field_id)
            .from_bytes_lfc1(&original, true)
            .unwrap();
        println!(
            "DECODE lfc1_ms={:.3}",
            start.elapsed().as_secs_f64() * 1000.
        );
        let start = Instant::now();
        let _ = core_proto::reader::CircuitReader::new(f, field_id)
            .from_bytes_lfc2(&lfc2, true)
            .unwrap();
        println!(
            "DECODE lfc2_ms={:.3}",
            start.elapsed().as_secs_f64() * 1000.
        );
        drop(lfc2);
    }
    for structural in [false, true] {
        let label = if structural { "structural" } else { "rank" };
        let bs = blocks(&graph, &ts, structural);
        correspondence(label, &bs, &graph, symbols);
        sequence_stats(
            &format!("{label}_absolute_subsequence_normalized"),
            bs.iter().map(|b| deltas(&b.absolute_local)),
        );
        sequence_stats(
            &format!("{label}_local_morton"),
            bs.iter().map(|b| deltas(&b.local)),
        );
        if !structural {
            let offsets = offset_sequences(&bs);
            sequence_stats(
                "offset_absolute_subsequence",
                offsets.iter().map(|b| deltas(&b.0)),
            );
            sequence_stats("offset_local_morton", offsets.iter().map(|b| deltas(&b.1)));
            sequence_stats(
                "offset_interior_absolute_subsequence",
                offsets.iter().map(|b| {
                    deltas(
                        &b.0.iter()
                            .filter(|t| t[1] as usize >= b.2 && t[2] as usize >= b.2)
                            .copied()
                            .collect::<Vec<_>>(),
                    )
                }),
            );
            sequence_stats(
                "offset_interior_local_morton",
                offsets.iter().map(|b| {
                    deltas(
                        &b.1.iter()
                            .filter(|t| t[1] as usize >= b.2 && t[2] as usize >= b.2)
                            .copied()
                            .collect::<Vec<_>>(),
                    )
                }),
            );
            let mut fragmented = HashSet::new();
            for b in &bs {
                if !b.outputs.windows(2).all(|p| p[1] == p[0] + 1) {
                    fragmented.insert(b.component);
                }
            }
            let contiguous_terms: usize = bs
                .iter()
                .filter(|b| !fragmented.contains(&b.component))
                .map(|b| b.local.len())
                .sum();
            let output_runs: usize = bs
                .iter()
                .map(|b| 1 + b.outputs.windows(2).filter(|p| p[1] != p[0] + 1).count())
                .sum();
            println!(
                "LAYOUT fragmented_components={} fully_contiguous_component_terms={contiguous_terms} output_mapping_runs={output_runs} component_layer_blocks={}",
                fragmented.len(),
                bs.len()
            );
            sequence_stats(
                "rank_absolute_subsequence_absolute_coords",
                bs.iter().map(|b| {
                    let absolute: Vec<_> = b
                        .absolute_local
                        .iter()
                        .map(|t| {
                            let a = b.inputs[t[1] as usize];
                            let h = b.inputs[t[2] as usize];
                            [b.outputs[t[0] as usize], a.min(h), a.max(h), t[3]]
                        })
                        .collect();
                    deltas(&absolute)
                }),
            );
            sequence_stats(
                "rank_interior_absolute_subsequence",
                bs.iter().map(|b| {
                    deltas(
                        &b.absolute_local
                            .iter()
                            .filter(|t| {
                                t[1] as usize >= b.ports.len() && t[2] as usize >= b.ports.len()
                            })
                            .copied()
                            .collect::<Vec<_>>(),
                    )
                }),
            );
            sequence_stats(
                "rank_interior_local_morton",
                bs.iter().map(|b| {
                    deltas(
                        &b.local
                            .iter()
                            .filter(|t| {
                                t[1] as usize >= b.ports.len() && t[2] as usize >= b.ports.len()
                            })
                            .copied()
                            .collect::<Vec<_>>(),
                    )
                }),
            );
        }
        if diagnostics_only {
            continue;
        }
        let encoded = encode(f, c, &bs);
        sizes(&format!("{label}_LCT0"), &encoded);
        let packed = zstd::bulk::compress(&encoded, 16).unwrap();
        let start = Instant::now();
        let unpacked = zstd::bulk::decompress(&packed, encoded.len()).unwrap();
        let recovered = decode(f, &unpacked);
        let ms = start.elapsed().as_secs_f64() * 1000.;
        assert_eq!(writer.to_bytes_lfc1(&recovered), original);
        println!(
            "ROUNDTRIP {label}: exact_lfc1=true exact_id=true decode_zstd16_expand_sort_hash_ms={ms:.3}"
        );
        drop(recovered);
        if !structural {
            let encoded = encode_grouped(f, c, &bs);
            sizes("rank_LCT1_grouped", &encoded);
            let packed = zstd::bulk::compress(&encoded, 16).unwrap();
            let start = Instant::now();
            let unpacked = zstd::bulk::decompress(&packed, encoded.len()).unwrap();
            let recovered = decode(f, &unpacked);
            let ms = start.elapsed().as_secs_f64() * 1000.;
            assert_eq!(writer.to_bytes_lfc1(&recovered), original);
            println!(
                "ROUNDTRIP rank_grouped: exact_lfc1=true exact_id=true decode_zstd16_expand_sort_hash_ms={ms:.3}"
            );
        }
        if !structural {
            let mut reordered = vec![Vec::new(); ts.len()];
            for b in &bs {
                for t in &b.local {
                    let a = b.inputs[t[1] as usize];
                    let h = b.inputs[t[2] as usize];
                    reordered[b.depth].push([b.outputs[t[0] as usize], a.min(h), a.max(h), t[3]]);
                }
            }
            let alternative = rebuild(f, c, reordered);
            sizes(
                "local_traversal_absolute_coords_lfc1",
                &writer.to_bytes_lfc1(&alternative),
            );
            let segmented = compile_compiler::segment_circuit(f, &alternative);
            sizes(
                "local_traversal_absolute_coords_lfc2",
                &writer.to_bytes_lfc2(&segmented),
            );
        }
    }
}

#[allow(dead_code)]
pub fn template_roundtrip<F: AlgebraicField + SerializableField>(
    f: &F,
    c: &Circuit<F>,
) -> Circuit<F> {
    let ts = terms(c);
    let graph = graph(f, c, &ts);
    let bs = blocks(&graph, &ts, false);
    decode(f, &encode_grouped(f, c, &bs))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_comparison_accepts_frequency_reindexed_constants() {
        let f = compile_algebra::p256::P256Field::new();
        let raw = RawCircuit {
            ninput: 2,
            npublic_input: 1,
            noutput: 2,
            logv: 1,
            subfield_boundary: 0,
            constants: vec![f.one(), f.mone()],
            layers: vec![Layer::new_compressed(
                2,
                1,
                vec![vec![
                    TermDelta {
                        g: 0,
                        h: [0, 1],
                        k_index: 1,
                    },
                    TermDelta {
                        g: 1,
                        h: [1, 0],
                        k_index: 1,
                    },
                ]],
                vec![0],
            )],
        };
        let c = Circuit {
            id: compute_id(&f, &raw),
            raw,
        };
        let segmented = compile_compiler::segment_circuit(&f, &c);
        assert_ne!(c.raw.constants, segmented.raw.constants);
        assert_same_terms(&f, &c, &segmented);
    }

    #[test]
    fn shared_inputs_and_copies_of_one_do_not_join_components() {
        let f = compile_algebra::gf2_128::Gf2_128Field::new();
        let c = Circuit {
            raw: RawCircuit {
                ninput: 2,
                npublic_input: 1,
                noutput: 3,
                logv: 2,
                subfield_boundary: 0,
                constants: vec![f.one()],
                layers: Vec::new(),
            },
            id: [0; 32],
        };
        // Both branches share input 1; both subsequently consume the copy of 1
        // at layer-one wire 0. Neither boundary should join the branches.
        let ts = vec![
            vec![[0, 0, 0, 0], [1, 0, 1, 0], [2, 1, 1, 0]],
            vec![[0, 0, 0, 0], [1, 0, 1, 0], [2, 0, 2, 0]],
        ];
        let g = graph(&f, &c, &ts);
        for d in 1..=2 {
            assert!(g.constants[g.offsets[d]].is_some());
            assert_ne!(
                g.components[g.offsets[d] + 1],
                g.components[g.offsets[d] + 2]
            );
            assert_ne!(g.components[g.offsets[d] + 1], g.components[1]);
        }
        assert_eq!(
            g.components[g.offsets[1] + 1],
            g.components[g.offsets[2] + 1]
        );
        assert_eq!(
            g.components[g.offsets[1] + 2],
            g.components[g.offsets[2] + 2]
        );
    }

    #[test]
    fn morton_translation_changes_order() {
        let a = [0, 0, 3, 0];
        let b = [0, 2, 2, 0];
        assert!(cmp(&a, &b).is_lt());
        assert!(cmp(&[0, 1, 4, 0], &[0, 3, 3, 0]).is_gt());
    }

    #[test]
    fn map_roundtrip_handles_permutations_and_shared_ports() {
        let maps = [
            vec![0, 10, 11, 12, 9, 55],
            vec![0, 100, 101, 102, 99, 145],
            vec![0, 12, 0, 1, 0, u32::MAX],
        ];
        let mut bytes = Vec::new();
        put_map(&mut bytes, &maps[0]);
        let mut previous = maps[0].clone();
        for map in &maps[1..] {
            put_map_difference(&mut bytes, map, &mut previous);
        }
        let mut input = bytes.as_slice();
        let mut recovered = get_map(&mut input);
        assert_eq!(recovered, maps[0]);
        for map in &maps[1..] {
            get_map_difference(&mut input, &mut recovered);
            assert_eq!(&recovered, map);
        }
        assert!(input.is_empty());
    }
}
