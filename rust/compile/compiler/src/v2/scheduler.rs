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

use super::terms::{CircuitGraph, Node, Term as NativeTerm};
use crate::{
    compile::{
        algebra::field::CompileField,
        compiler::scheduling::{
            extract_debug_symbols, validate_and_count_inputs, RenamedNode, RenamedTerm, WireId,
            INVALID_WIRE_ID,
        },
        logic::scope::AssertionId,
    },
    core::proto::CircuitGeometry,
    util::ceil_log2,
};

// Assert that all nodes in the circuit are needed
fn assert_all_needed<F: CompileField>(f: &F, nodes: &[Node<F>]) {
    let mut needed = vec![false; nodes.len()];
    for i in (0..nodes.len()).rev() {
        match &nodes[i] {
            Node::Input { .. } => {
                assert!(needed[i], "found input that is not needed");
            }
            Node::Assert0(w) => {
                needed[i] = true;
                needed[*w] = true;
            }
            Node::Sum(terms) => {
                if terms.len() == 1 && f.is_zero(terms[0].coefficient()) {
                    needed[i] = true;
                }
                assert!(needed[i]);
                for term in terms {
                    for &wire in term.inputs() {
                        needed[wire] = true;
                    }
                }
            }
        }
    }
}

// Depth of node assuming children depth has already been computed
fn depth_of_node<F: CompileField>(depth: &[usize], node: &Node<F>) -> usize {
    match node {
        Node::Input { .. } => 0,
        Node::Assert0(w) => depth[*w],
        Node::Sum(terms) => {
            assert!(!terms.is_empty(), "empty quad in circuit!");
            terms
                .iter()
                .map(|term| 1 + term.inputs().iter().map(|&w| depth[w]).max().unwrap_or(0))
                .max()
                .unwrap_or(0)
        }
    }
}

fn assert_layering<F: CompileField>(f: &F, depth: &[usize], i: usize, node: &Node<F>) {
    match node {
        Node::Input { .. } => assert_eq!(depth[i], 0),
        Node::Assert0(w) => assert_eq!(depth[i], depth[*w]),
        Node::Sum(terms) => {
            assert!(!terms.is_empty(), "empty quad in circuit!");
            for term in terms {
                assert!(
                    !f.is_zero(term.coefficient()) || terms.len() == 1,
                    "zero coefficient outside assertion"
                );
                for &wire in term.inputs() {
                    assert_eq!(depth[i], depth[wire] + 1);
                }
            }
        }
    }
}

// Materialize all in-circuit assertions into quad nodes. Assertions
// in the last layer become outputs and are not instantiated.
fn materialize_assertions<F: CompileField>(
    f: &F,
    nodes: &mut [Node<F>],
    depth: &mut [usize],
    max_depth: usize,
) {
    for i in 0..nodes.len() {
        if let Node::Assert0(w) = nodes[i] {
            if depth[i] < max_depth {
                nodes[i] = Node::Sum(vec![NativeTerm::Linear(f.zero(), w)]);
                depth[i] += 1;
            }
        }
    }
}

fn assign_wire_ids<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    nodes: &[Node<F>],
    nodes_by_depth: &[Vec<usize>],
    max_depth: usize,
) -> Vec<WireId> {
    let mut ids = vec![INVALID_WIRE_ID; nodes.len()];

    // Depth 0: Inputs
    if !nodes_by_depth.is_empty() {
        for &i in &nodes_by_depth[0] {
            if let Node::Input {
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
            if let Node::Sum(terms) = &nodes[i] {
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
                for term in terms {
                    // Unit factors sort before real inputs, without allocating a One wire.
                    let (a, b) = match term {
                        NativeTerm::Quadratic(_, [left, right]) => (
                            ids[*left].id_within_layer + 1,
                            ids[*right].id_within_layer + 1,
                        ),
                        NativeTerm::Linear(_, wire) => (0, ids[*wire].id_within_layer + 1),
                        NativeTerm::Constant(_) => (0, 0),
                    };
                    rlterms.push(RenamedTerm {
                        k: term.coefficient().clone(),
                        rlop0: a.min(b),
                        rlop1: a.max(b),
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

struct ScheduledTerm<F: CompileField> {
    g: u32,
    term: NativeTerm<F>,
}

fn collect_terms<F: CompileField + crate::core::algebra::SerializableField>(
    nodes: &[Node<F>],
    nodes_by_depth: &[Vec<usize>],
    max_depth: usize,
    ids: &[WireId],
) -> (Vec<Vec<ScheduledTerm<F>>>, Vec<usize>) {
    let mut terms_in_layer: Vec<Vec<ScheduledTerm<F>>> =
        (0..max_depth).map(|_| Vec::new()).collect();
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
            if let Node::Sum(terms) = &nodes[i] {
                layer_nodes.push((i, terms));
            }
        }
        layer_nodes.sort_unstable_by_key(|&(i, _)| ids[i].id_within_layer);
        nwires_in_layer[level] = layer_nodes.len();

        for &(i, terms) in &layer_nodes {
            let g = ids[i].id_within_layer as u32;
            for term in terms {
                terms_in_layer[level].push(ScheduledTerm {
                    g,
                    term: term.rename(|wire| ids[wire].id_within_layer),
                });
            }
        }
    }

    (terms_in_layer, nwires_in_layer)
}

fn check_connectivity<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    ninput: usize,
    noutput: usize,
    terms_in_layer: &[Vec<ScheduledTerm<F>>],
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
                for &wire in term.term.inputs() {
                    visited[wire] = true;
                }
                if f.is_zero(term.term.coefficient()) {
                    arr[term.g as usize] = true;
                }
            }
            arr
        };
        for (i, &val) in visited.iter().enumerate() {
            assert!(val, "unvisited wire {i} in layer {l}");
        }
        v = assertions;
    }
}

fn compute_node_depths<F: CompileField>(f: &F, nodes: &mut [Node<F>]) -> (Vec<usize>, usize) {
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
            nodes.iter().any(|node| matches!(node, Node::Assert0(_))),
            "circuit with no depth makes no sense"
        );
        1
    } else {
        raw_max_depth
    };
    materialize_assertions(f, nodes, &mut depth, max_depth);
    (depth, max_depth)
}

struct Scheduled<F: CompileField> {
    terms: Vec<Vec<ScheduledTerm<F>>>,
    widths: Vec<usize>,
    constants: Vec<F::E>,
    constant_to_idx: std::collections::HashMap<Vec<u8>, u32>,
    info: CircuitGeometry,
    symbols: crate::compile::compiler::debug::CircuitDebugSymbols,
}

fn schedule_graph<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    c: CircuitGraph<F>,
    quad_asserts: &[(usize, AssertionId)],
    npublic_input: usize,
    tracker: crate::compile::logic::scope::AssertionScope,
) -> Scheduled<F> {
    let npublic_input = npublic_input
        .checked_sub(1)
        .expect("source public-input boundary must be at least 1");
    let mut nodes = c.nodes;
    let nassertions = nodes
        .iter()
        .filter(|node| {
            matches!(node, Node::Assert0(_))
                || matches!(node,Node::Sum(t) if t.len()==1 && f.is_zero(t[0].coefficient()))
        })
        .count();
    assert_eq!(
        quad_asserts.len(),
        nassertions,
        "debug assertion records do not cover all circuit assertions"
    );
    assert_all_needed(f, &nodes);

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
        collect_terms(&nodes, &nodes_by_depth, max_depth, &wire_ids);

    let ninput = validate_and_count_inputs(&nodes);
    assert!(
        npublic_input <= ninput,
        "npublic_input ({npublic_input}) exceeds ninput ({ninput})"
    );
    let noutput = nwires_in_layer[max_depth - 1];

    check_connectivity(f, ninput, noutput, &terms_in_layer, &nwires_in_layer);

    let (constants, constant_to_idx) = collect_constants(f, &terms_in_layer);

    let info = CircuitGeometry {
        ninput,
        npublic_input,
        noutput,
        nlayers: terms_in_layer.len(),
        nwires: nwires_in_layer.iter().sum(),
        nterms: terms_in_layer.iter().map(Vec::len).sum(),
        nassertions,
    };
    Scheduled {
        terms: terms_in_layer,
        widths: nwires_in_layer,
        constants,
        constant_to_idx,
        info,
        symbols,
    }
}

pub(super) fn schedule<F: CompileField>(
    f: &F,
    c: CircuitGraph<F>,
    assertions: &[(usize, AssertionId)],
    npublic_input: usize,
    tracker: crate::compile::logic::scope::AssertionScope,
) -> (
    crate::core::proto::v2::Circuit<F>,
    CircuitGeometry,
    crate::compile::compiler::debug::CircuitDebugSymbols,
) {
    let graph = schedule_graph(f, c, assertions, npublic_input, tracker);
    let layers = v2_layers(
        f,
        graph.terms,
        graph.info.ninput,
        &graph.widths,
        &graph.constant_to_idx,
    )
    .into_iter()
    .rev()
    .collect();
    let raw = crate::core::proto::v2::RawCircuitBuilder {
        ninput: graph.info.ninput,
        npublic_input: graph.info.npublic_input,
        noutput: graph.info.noutput,
        logv: ceil_log2(graph.info.noutput),
        constants: graph.constants,
        layers,
    }
    .build();
    let id = crate::core::proto::v2::compute_id(f, &raw);
    (
        crate::core::proto::v2::Circuit::new(id, raw),
        graph.info,
        graph.symbols,
    )
}

fn collect_constants<F: CompileField>(
    f: &F,
    terms_in_layer: &[Vec<ScheduledTerm<F>>],
) -> (Vec<F::E>, std::collections::HashMap<Vec<u8>, u32>) {
    let mut constants = Vec::new();
    let mut constant_to_idx = std::collections::HashMap::new();

    for layer in terms_in_layer {
        for term in layer {
            let key = f.to_bytes(term.term.coefficient());
            constant_to_idx.entry(key).or_insert_with(|| {
                let idx = constants.len() as u32;
                constants.push(term.term.coefficient().clone());
                idx
            });
        }
    }

    (constants, constant_to_idx)
}

fn v2_layers<F: CompileField + crate::core::algebra::SerializableField>(
    f: &F,
    terms: Vec<Vec<ScheduledTerm<F>>>,
    ninput: usize,
    widths: &[usize],
    constants: &std::collections::HashMap<Vec<u8>, u32>,
) -> Vec<crate::core::proto::v2::Layer> {
    let mut nw = ninput;
    terms
        .into_iter()
        .enumerate()
        .map(|(i, terms)| {
            let mut streams: [Vec<ScheduledTerm<F>>; 3] = std::array::from_fn(|_| Vec::new());
            for term in terms {
                let stream = match term.term {
                    NativeTerm::Quadratic(..) => 0,
                    NativeTerm::Linear(..) => 1,
                    NativeTerm::Constant(..) => 2,
                };
                streams[stream].push(term);
            }
            for stream in &mut streams {
                let key = |t: &ScheduledTerm<F>| {
                    let (shape, left, right) = match &t.term {
                        NativeTerm::Quadratic(_, [left, right]) => {
                            (usize::from(left != right), *left, *right)
                        }
                        NativeTerm::Linear(_, wire) => (0, *wire, 0),
                        NativeTerm::Constant(_) => (0, 0, 0),
                    };
                    (
                        shape,
                        std::cmp::Reverse(t.g),
                        std::cmp::Reverse(right),
                        left,
                    )
                };
                stream.sort_unstable_by(|a, b| {
                    key(a).cmp(&key(b)).then_with(|| {
                        f.to_bytes(a.term.coefficient())
                            .cmp(&f.to_bytes(b.term.coefficient()))
                    })
                });
            }
            let [q, l, c] = streams;
            let layer = build_v2_layer(f, constants, q, l, c, nw);
            nw = widths[i];
            layer
        })
        .collect()
}

fn build_v2_layer<F: CompileField>(
    f: &F,
    constants: &std::collections::HashMap<Vec<u8>, u32>,
    quadratic: Vec<ScheduledTerm<F>>,
    linear: Vec<ScheduledTerm<F>>,
    constant: Vec<ScheduledTerm<F>>,
    nw: usize,
) -> crate::core::proto::v2::Layer {
    use crate::core::proto::v2::{Constant, Layer, Linear, Quadratic, Stream};
    let quadratic = Stream::<Quadratic>::from_terms(quadratic.into_iter().map(|t| {
        let NativeTerm::Quadratic(k, [left, right]) = t.term else {
            unreachable!("quadratic stream")
        };
        Quadratic {
            g: t.g,
            l: left as u32,
            r: right as u32,
            k: constants[&f.to_bytes(&k)],
        }
    }));
    let linear = Stream::<Linear>::from_terms(linear.into_iter().map(|t| {
        let NativeTerm::Linear(k, wire) = t.term else {
            unreachable!("linear stream")
        };
        Linear {
            g: t.g,
            l: wire as u32,
            k: constants[&f.to_bytes(&k)],
        }
    }));
    let constant = Stream::<Constant>::from_terms(constant.into_iter().map(|t| {
        let NativeTerm::Constant(k) = t.term else {
            unreachable!("constant stream")
        };
        assert!(!f.is_zero(&k), "constant assertions are unsupported");
        Constant {
            g: t.g,
            k: constants[&f.to_bytes(&k)],
        }
    }));
    let zero = constants.get(&f.to_bytes(&f.zero())).copied();
    Layer::with_assertions(nw, quadratic, linear, constant, |k| Some(k) == zero)
}
