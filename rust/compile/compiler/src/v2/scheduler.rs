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

//! Longfellow v2 wire scheduling and circuit encoding.

use super::term_order;
use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::quad::{QuadCircuit, WExpr},
    },
    core::{
        algebra::ElementOf,
        proto::circuit::{
            canonical_term, compare_term, compute_id, Circuit, CircuitGeometry, Layer, RawCircuit,
            Term, TermDelta,
        },
    },
    util::ceil_log2,
};

// Assert that all nodes in the circuit are needed
fn assert_all_needed<F: CompileField>(nodes: &[WExpr<F>]) {
    let mut needed = vec![false; nodes.len()];
    for i in (0..nodes.len()).rev() {
        match &nodes[i] {
            WExpr::Unspecified => panic!("Unspecified in circuit"),
            WExpr::Input { .. } => {
                if needed[i] || i == 0 {
                    // input is needed (or i==0 which is the reserved constant One), valid
                } else {
                    panic!("found input that is not needed");
                }
            }
            WExpr::Assert0(w) => {
                needed[i] = true;
                needed[*w] = true;
            }
            WExpr::Sum(terms) => {
                assert!(needed[i]);
                for (_, w0, w1) in terms {
                    needed[*w0] = true;
                    needed[*w1] = true;
                }
            }
        }
    }
}

// Depth of node assuming children depth has already been computed
fn depth_of_node<F: CompileField>(depth: &[usize], node: &WExpr<F>) -> usize {
    match node {
        WExpr::Unspecified => panic!("Unspecified in circuit"),
        WExpr::Input { .. } => 0,
        WExpr::Assert0(w) => depth[*w],
        WExpr::Sum(terms) => {
            assert!(!terms.is_empty(), "empty quad in circuit!");
            terms
                .iter()
                .map(|(_, x, y)| 1 + std::cmp::max(depth[*x], depth[*y]))
                .max()
                .unwrap_or(0)
        }
    }
}

fn assert_layering<F: CompileField>(f: &F, depth: &[usize], i: usize, node: &WExpr<F>) {
    match node {
        WExpr::Unspecified => panic!("Unspecified in circuit"),
        WExpr::Input { .. } => assert_eq!(depth[i], 0),
        WExpr::Assert0(w) => assert_eq!(depth[i], depth[*w]),
        WExpr::Sum(terms) => {
            assert!(!terms.is_empty(), "empty quad in circuit!");
            for (e, x, y) in terms {
                assert!(!f.is_zero(e));
                assert_eq!(depth[i], depth[*x] + 1);
                assert_eq!(depth[i], depth[*y] + 1);
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct WireId {
    id_within_layer: usize,
}

const INVALID_WIRE_ID: WireId = WireId {
    id_within_layer: usize::MAX,
};

// Materialize all in-circuit assertions into quad nodes. Assertions
// in the last layer become outputs and are not instantiated.
fn materialize_assertions<F: CompileField>(
    f: &F,
    nodes: &mut [WExpr<F>],
    depth: &mut [usize],
    max_depth: usize,
) {
    for i in 0..nodes.len() {
        if let WExpr::Assert0(w) = nodes[i] {
            if depth[i] < max_depth {
                nodes[i] = WExpr::Sum(vec![(f.zero(), w, w)]);
                depth[i] += 1;
            }
        }
    }
}

struct RenamedTerm<F: CompileField + crate::core::algebra::SerializableField> {
    k: ElementOf<F>,
    rlop0: usize,
    rlop1: usize,
}

impl<F: CompileField + crate::core::algebra::SerializableField> RenamedTerm<F> {
    fn compare(&self, other: &Self, f: &F) -> std::cmp::Ordering {
        self.rlop1
            .cmp(&other.rlop1)
            .then(self.rlop0.cmp(&other.rlop0))
            .then_with(|| f.to_bytes(&self.k).cmp(&f.to_bytes(&other.k)))
    }
}

struct RenamedNode<F: CompileField + crate::core::algebra::SerializableField> {
    original_node_index: usize,
    rlterms: Vec<RenamedTerm<F>>,
}

impl<F: CompileField + crate::core::algebra::SerializableField> RenamedNode<F> {
    fn compare(&self, other: &Self, f: &F) -> std::cmp::Ordering {
        let mut ia = self.rlterms.len();
        let mut ib = other.rlterms.len();
        while ia > 0 && ib > 0 {
            ia -= 1;
            ib -= 1;
            let ord = self.rlterms[ia].compare(&other.rlterms[ib], f);
            if ord != std::cmp::Ordering::Equal {
                return ord;
            }
        }

        let len_ord = other.rlterms.len().cmp(&self.rlterms.len());
        if len_ord != std::cmp::Ordering::Equal {
            return len_ord;
        }

        assert_eq!(
            self.original_node_index, other.original_node_index,
            "Compare tie-break occurred: duplicate node detected"
        );
        other.original_node_index.cmp(&self.original_node_index)
    }
}

fn assign_wire_ids<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    nodes: &[WExpr<F>],
    nodes_by_depth: &[Vec<usize>],
    max_depth: usize,
) -> Vec<WireId> {
    let mut ids = vec![INVALID_WIRE_ID; nodes.len()];

    // Depth 0: Inputs
    if !nodes_by_depth.is_empty() {
        for &i in &nodes_by_depth[0] {
            if let WExpr::Input {
                position_in_input_array,
            } = &nodes[i]
            {
                ids[i] = WireId {
                    id_within_layer: *position_in_input_array,
                };
            }
        }
    }

    // Depth 1 to max_depth: Gates
    for nodes_at_d in nodes_by_depth.iter().take(max_depth + 1).skip(1) {
        let mut layer_nodes = Vec::new();
        for &i in nodes_at_d {
            if let WExpr::Sum(terms) = &nodes[i] {
                layer_nodes.push((i, terms));
            }
        }
        if layer_nodes.is_empty() {
            continue;
        }

        let mut renamed_nodes: Vec<RenamedNode<F>> = layer_nodes
            .into_iter()
            .map(|(i, terms)| {
                let mut rlterms = Vec::with_capacity(terms.len());
                for &(ref e, w0, w1) in terms {
                    let rlop0 = ids[w0].id_within_layer;
                    let rlop1 = ids[w1].id_within_layer;
                    rlterms.push(RenamedTerm {
                        k: e.clone(),
                        rlop0: std::cmp::min(rlop0, rlop1),
                        rlop1: std::cmp::max(rlop0, rlop1),
                    });
                }
                rlterms.sort_by(|a, b| a.compare(b, f));
                for idx in 1..rlterms.len() {
                    assert!(
                        rlterms[idx - 1].compare(&rlterms[idx], f) != std::cmp::Ordering::Equal,
                        "Scheduler: duplicate term detected (no coalescing allowed)"
                    );
                }
                RenamedNode {
                    original_node_index: i,
                    rlterms,
                }
            })
            .collect();

        renamed_nodes.sort_by(|a, b| a.compare(b, f));

        // Assign wire IDs sequentially
        for (wid, rn) in renamed_nodes.iter().enumerate() {
            ids[rn.original_node_index] = WireId {
                id_within_layer: wid,
            };
        }
    }

    ids
}

fn collect_quads<F: CompileField + crate::core::algebra::SerializableField>(
    nodes: &[WExpr<F>],
    nodes_by_depth: &[Vec<usize>],
    max_depth: usize,
    ids: &[WireId],
) -> (Vec<Vec<Term<F>>>, Vec<usize>) {
    let mut terms_in_layer: Vec<Vec<Term<F>>> = (0..max_depth).map(|_| Vec::new()).collect();
    let mut nwires_in_layer = vec![0; max_depth];

    for (d, nodes_at_d) in nodes_by_depth
        .iter()
        .enumerate()
        .take(max_depth + 1)
        .skip(1)
    {
        let level = d - 1;
        let mut layer_nodes = Vec::new();
        for &i in nodes_at_d {
            if let WExpr::Sum(terms) = &nodes[i] {
                layer_nodes.push((i, terms));
            }
        }
        layer_nodes.sort_unstable_by_key(|&(i, _)| ids[i].id_within_layer);
        nwires_in_layer[level] = layer_nodes.len();

        for &(i, terms) in &layer_nodes {
            let g = ids[i].id_within_layer as u32;
            for &(ref e, w0, w1) in terms {
                let term = canonical_term(Term {
                    k: e.clone(),
                    g,
                    h0: ids[w0].id_within_layer as u32,
                    h1: ids[w1].id_within_layer as u32,
                });
                terms_in_layer[level].push(term);
            }
        }
    }

    (terms_in_layer, nwires_in_layer)
}

fn check_connectivity<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    ninput: usize,
    noutput: usize,
    terms_in_layer: &[Vec<Term<F>>],
    nwires_in_layer: &[usize],
) {
    assert!(ninput > 0);
    let mut v = vec![false; ninput];
    for l in 0..terms_in_layer.len() {
        let layer_noutput = if l == terms_in_layer.len() - 1 {
            noutput
        } else {
            nwires_in_layer[l]
        };
        let mut visited = v;
        let assertions = {
            let mut arr = vec![false; layer_noutput];
            for term in &terms_in_layer[l] {
                visited[term.h0 as usize] = true;
                visited[term.h1 as usize] = true;
                if f.is_zero(&term.k) {
                    arr[term.g as usize] = true;
                }
            }
            arr
        };
        for (i, &val) in visited.iter().enumerate() {
            assert!(val || (l == 0 && i == 0), "unvisited wire {i} in layer {l}");
        }
        v = assertions;
    }
}

fn compute_node_depths<F: CompileField>(f: &F, nodes: &mut [WExpr<F>]) -> (Vec<usize>, usize) {
    let mut depth = vec![0; nodes.len()];
    for i in 0..nodes.len() {
        depth[i] = depth_of_node(&depth, &nodes[i]);
    }
    for (i, node) in nodes.iter().enumerate() {
        assert_layering(f, &depth, i, node);
    }
    let raw_max_depth = depth.iter().max().copied().unwrap_or(0);
    // Final-layer assertions normally reuse their asserted wires as circuit
    // outputs. A depth-zero circuit has no layer whose wires can serve as
    // outputs, so materialize its assertions in a single assertion layer.
    let max_depth = if raw_max_depth == 0 {
        assert!(
            nodes.iter().any(|node| matches!(node, WExpr::Assert0(_))),
            "circuit with no depth makes no sense"
        );
        1
    } else {
        raw_max_depth
    };
    materialize_assertions(f, nodes, &mut depth, max_depth);
    (depth, max_depth)
}

fn validate_and_count_inputs<F: CompileField>(nodes: &[WExpr<F>]) -> usize {
    let mut ninput_wires = 0;
    let mut max_input_pos = 0;
    for n in nodes {
        if let WExpr::Input {
            position_in_input_array,
        } = n
        {
            ninput_wires += 1;
            max_input_pos = std::cmp::max(max_input_pos, *position_in_input_array);
        }
    }
    let ninput_positions = 1 + max_input_pos;
    if ninput_wires == ninput_positions {
        ninput_wires
    } else {
        panic!("some inputs are unused, cannot schedule");
    }
}

use crate::compile::logic::scope::AssertionId;

fn extract_debug_symbols<F: CompileField>(
    nodes: &[WExpr<F>],
    quad_asserts: &[(usize, AssertionId)],
    wire_ids: &[WireId],
    depth: &[usize],
    max_depth: usize,
    tracker: crate::compile::logic::scope::AssertionScope,
) -> crate::compile::compiler::debug::CircuitDebugSymbols {
    let mut sym_list = Vec::new();
    for &(quad_idx, id) in quad_asserts {
        if quad_idx < nodes.len() {
            let target_idx = match nodes[quad_idx] {
                WExpr::Assert0(w) => w,
                _ => quad_idx,
            };
            if target_idx < wire_ids.len() {
                let wid = wire_ids[target_idx].id_within_layer;
                if wid != usize::MAX {
                    let layer = max_depth
                        .checked_sub(depth[target_idx])
                        .expect("assertion target is deeper than the circuit");
                    let wire = crate::compile::compiler::debug::WireRef::new(layer, wid);
                    sym_list.push(crate::compile::compiler::debug::AssertionSymbol::new(
                        wire, id,
                    ));
                }
            }
        }
    }
    sym_list.sort_by_key(|s| (s.wire.layer, s.wire.index));
    crate::compile::compiler::debug::CircuitDebugSymbols::new(sym_list, tracker)
}

/// Transform the Quad circuit into a structured multi-layered Circuit with debug symbol extraction.
pub(super) fn schedule<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    c: QuadCircuit<F>,
    quad_asserts: &[(usize, AssertionId)],
    npublic_input: usize,
    subfield_boundary: usize,
    tracker: crate::compile::logic::scope::AssertionScope,
) -> (
    Circuit<F>,
    CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
) {
    let mut nodes = c.nodes;
    let nassertions = nodes
        .iter()
        .filter(|node| matches!(node, WExpr::Assert0(_)))
        .count();
    assert_eq!(
        quad_asserts.len(),
        nassertions,
        "debug assertion records do not cover all circuit assertions"
    );
    assert_all_needed(&nodes);

    let (depth, max_depth) = compute_node_depths(f, &mut nodes);

    let mut nodes_by_depth = vec![Vec::new(); max_depth + 1];
    for (i, &d) in depth.iter().enumerate() {
        nodes_by_depth[d].push(i);
    }

    let wire_ids = assign_wire_ids(f, &nodes, &nodes_by_depth, max_depth);

    let symbols =
        extract_debug_symbols(&nodes, quad_asserts, &wire_ids, &depth, max_depth, tracker);
    assert_eq!(
        symbols.assertion_count(),
        nassertions,
        "debug symbols do not cover all circuit assertions"
    );

    let (terms_in_layer, nwires_in_layer) =
        collect_quads(&nodes, &nodes_by_depth, max_depth, &wire_ids);

    let ninput = validate_and_count_inputs(&nodes);
    assert!(
        npublic_input >= 1,
        "npublic_input must include the reserved constant One"
    );
    assert!(
        npublic_input <= ninput,
        "npublic_input ({npublic_input}) exceeds ninput ({ninput})"
    );
    assert!(
        subfield_boundary <= ninput,
        "subfield_boundary ({subfield_boundary}) exceeds ninput ({ninput})"
    );
    let noutput = nwires_in_layer[max_depth - 1];

    check_connectivity(f, ninput, noutput, &terms_in_layer, &nwires_in_layer);

    let (constants, constant_to_idx) = collect_constants(f, &terms_in_layer);

    let c_layers = ordered_layers(
        f,
        terms_in_layer,
        ninput,
        &nwires_in_layer,
        &constant_to_idx,
    );

    let nwires = nwires_in_layer.iter().sum();
    let total_terms = c_layers
        .iter()
        .map(crate::core::proto::Layer::num_terms)
        .sum();

    let info = CircuitGeometry {
        ninput,
        npublic_input,
        noutput,
        nlayers: c_layers.len(),
        nwires,
        nterms: total_terms,
        nassertions,
    };

    let layers: Vec<Layer<F>> = c_layers.into_iter().rev().collect();

    let raw_circuit = RawCircuit {
        ninput,
        npublic_input,
        noutput,
        logv: ceil_log2(noutput),
        subfield_boundary: 0,
        constants,
        layers,
    };

    let id = compute_id(f, &raw_circuit);

    (
        Circuit {
            raw: raw_circuit,
            id,
        },
        info,
        symbols,
    )
}

/// Propagate constants and arrange terms in the v2 output-major traversal.
fn ordered_layers<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    terms_in_layer: Vec<Vec<Term<F>>>,
    ninput: usize,
    nwires_in_layer: &[usize],
    constant_to_idx: &std::collections::HashMap<Vec<u8>, u32>,
) -> Vec<Layer<F>> {
    let mut known_inputs = vec![None; ninput];
    known_inputs[0] = Some(f.one());
    let mut layers = Vec::with_capacity(terms_in_layer.len());
    for (i, mut terms) in terms_in_layer.into_iter().enumerate() {
        let nw = known_inputs.len();
        let nv = nwires_in_layer[i];
        known_inputs = term_order::order_layer(f, &mut terms, &known_inputs, nv);
        layers.push(build_layer(f, constant_to_idx, terms, nw, ceil_log2(nw)));
    }
    layers
}

fn collect_constants<F: CompileField>(
    f: &F,
    terms_in_layer: &[Vec<Term<F>>],
) -> (Vec<F::E>, std::collections::HashMap<Vec<u8>, u32>) {
    let mut constants = Vec::new();
    let mut constant_to_idx = std::collections::HashMap::new();

    for layer in terms_in_layer {
        for term in layer {
            let key = f.to_bytes(&term.k);
            constant_to_idx.entry(key).or_insert_with(|| {
                let idx = constants.len() as u32;
                constants.push(term.k.clone());
                idx
            });
        }
    }

    (constants, constant_to_idx)
}

fn build_layer<F: CompileField>(
    f: &F,
    constant_to_idx: &std::collections::HashMap<Vec<u8>, u32>,
    layer_sorted: Vec<Term<F>>,
    layer_ninput: usize,
    logw: usize,
) -> Layer<F> {
    for idx in 1..layer_sorted.len() {
        assert!(
            compare_term(f, &layer_sorted[idx - 1], &layer_sorted[idx])
                != std::cmp::Ordering::Equal,
            "Scheduler: duplicate term detected in layer outputs (no coalescing allowed)"
        );
    }

    // Preserve traversal order directly. Layer construction owns dictionary
    // compression; building and expanding another dictionary here adds no data.
    let mut deltas = Vec::with_capacity(layer_sorted.len());
    let mut prev_g = 0u32;
    let mut prev_h0 = 0u32;
    let mut prev_h1 = 0u32;

    for term in layer_sorted {
        let key = f.to_bytes(&term.k);
        let k_index = constant_to_idx[&key];

        let dg = term.g.wrapping_sub(prev_g);
        let dh0 = term.h0.wrapping_sub(prev_h0);
        let dh1 = term.h1.wrapping_sub(prev_h1);

        deltas.push(TermDelta {
            g: dg,
            h: [dh0, dh1],
            k_index,
        });

        prev_g = term.g;
        prev_h0 = term.h0;
        prev_h1 = term.h1;
    }

    Layer::new_compressed(layer_ninput, logw, vec![deltas], vec![0])
}
