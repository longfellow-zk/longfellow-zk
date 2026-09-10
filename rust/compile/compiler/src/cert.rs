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

//! Certificate sidecar for compiled circuits.
//!
//! Implements Phase R0 of `formal/circuits/CIRCUIT_PROOF_PLAN.md`: a
//! deterministic byte dump of everything the Lean endpoint checker needs to
//! verify that a compiled quad circuit computes what its named assertions
//! claim.
//!
//! The sidecar is *advice*: every byte of it is re-checked in Lean against
//! the production circuit. To keep a bogus sidecar from being produced in the
//! first place, [`build_sidecar`] additionally verifies at construction time
//! that the dumped DAG together with the wire map reproduces the shipped
//! circuit term by term (see `check_dag_reproduces_circuit`).
//!
//! Byte layout (all integers little-endian):
//!
//! ```text
//! magic [8] = "LFZKCRT1"
//! version u32
//! field_id u32
//! circuit id [32]
//! elt_size u32
//! ninput u64, npublic_input u64, noutput u64, logv u64, subfield_boundary u64
//! nconstants u32, then nconstants elements of elt_size bytes
//! nlayers u32
//! per layer: nw u64, logw u64, nterms u64,
//!            per term: g u32, h0 u32, h1 u32, k_index u32   (canonical order)
//! nnodes u64
//! per node: tag u8 (0 = Input, 1 = Sum, 2 = Assert0)
//!   Input:   position u32
//!   Sum:     nterms u32, per term: k_index u32, w0 u32, w1 u32
//!   Assert0: w u32
//! per node: present u8; if 1: layer u32, index u32
//!           (input nodes sit at the pseudo-layer nlayers)
//! nassertions u32
//! per assertion (sorted by wire coordinates):
//!   assert_node u32, asserted_node u32, wire_layer u32, wire_index u32,
//!   npaths u32, per path: len u32 + utf8 bytes
//! nlayout u32
//! per layout entry: position u32, len u32 + utf8 bytes
//! magic [8]
//! ```

use compile_algebra::field::CompileField;
use core_algebra::SerializableField;
use core_proto::circuit::{compute_id, Circuit, FieldID, RawCircuit};
use core_proto::layer::{compare_term, Layer, Term, TermDelta};

use crate::debug::CircuitDebugSymbols;
use crate::quad::WExpr;
use crate::scheduler::ScheduleInfo;

pub const CERT_MAGIC: [u8; 8] = *b"LFZKCRT1";
pub const CERT_VERSION: u32 = 2;

const TAG_INPUT: u8 = 0;
const TAG_SUM: u8 = 1;
const TAG_ASSERT0: u8 = 2;

/// A human-readable name for one input position. The layout table is advice
/// for the spec bridge; it is reviewed once, not trusted blindly.
#[derive(Debug, Clone, Copy)]
pub struct InputLayoutEntry<'a> {
    pub position: usize,
    pub name: &'a str,
}

/// A node of an assertion **template**: the structural shape of an asserted sub-DAG with
/// its leaves abstracted into holes.
///
/// Measured on ECDSA2, 1,048 assertions share only ~52 shapes, so a meaning lemma proved
/// once per template and applied per instance replaces ~20x as many bespoke proofs. The
/// instances cannot be indexed arithmetically — their node indices, input positions and even
/// leaf counts are irregular, because `assign_wire_ids` re-sorts every layer — so a template
/// is parameterised by its **leaves**, which each instance supplies.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TemplateNode {
    /// A hole; the instance supplies the actual DAG node.
    Leaf(u32),
    /// `(k_index, child, child)` with children indexing this template's own node list.
    Sum(Vec<(u32, u32, u32)>),
}

/// A template: nodes in topological order, root last.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Template {
    pub nodes: Vec<TemplateNode>,
    pub nleaves: usize,
}

/// How far to expand a template before abstracting into holes. Expansion also stops at
/// input nodes and at nodes shared by more than one parent (CSE'd sub-expressions), which
/// is what makes the boundaries natural rather than arbitrary.
pub const TEMPLATE_DEPTH: usize = 8;

fn refcounts<F: CompileField>(nodes: &[WExpr<F>]) -> Vec<u32> {
    let mut rc = vec![0u32; nodes.len()];
    for n in nodes {
        match n {
            WExpr::Sum(ts) => {
                for (_, a, b) in ts {
                    rc[*a] += 1;
                    rc[*b] += 1;
                }
            }
            WExpr::Assert0(w) => rc[*w] += 1,
            _ => {}
        }
    }
    rc
}

/// Extracts the template rooted at `root`, together with the DAG node corresponding to each
/// of its template nodes (holes *and* internal nodes).
fn extract_template<F: CompileField>(
    nodes: &[WExpr<F>],
    rc: &[u32],
    k_index: &impl Fn(&F::E) -> u32,
    root: usize,
) -> (Template, Vec<u32>) {
    let mut tnodes: Vec<TemplateNode> = Vec::new();
    let mut leaves: Vec<u32> = Vec::new();
    // DAG node corresponding to each template node — the schema takes all of them as
    // parameters, since its internal nodes need structural hypotheses too.
    let mut tmap: Vec<u32> = Vec::new();
    // memoise by (dag node, remaining depth) so shared structure inside one template is
    // emitted once
    let mut memo: rustc_hash::FxHashMap<(usize, usize), u32> = rustc_hash::FxHashMap::default();

    fn go<F: CompileField>(
        nodes: &[WExpr<F>],
        rc: &[u32],
        k_index: &impl Fn(&F::E) -> u32,
        n: usize,
        depth: usize,
        is_root: bool,
        tnodes: &mut Vec<TemplateNode>,
        leaves: &mut Vec<u32>,
        tmap: &mut Vec<u32>,
        memo: &mut rustc_hash::FxHashMap<(usize, usize), u32>,
    ) -> u32 {
        if let Some(&i) = memo.get(&(n, depth)) {
            return i;
        }
        let shared = !is_root && rc[n] > 1;
        let expand = matches!(nodes[n], WExpr::Sum(_)) && depth > 0 && !shared;
        let idx = if expand {
            let WExpr::Sum(ts) = &nodes[n] else {
                unreachable!()
            };
            let mut terms = Vec::with_capacity(ts.len());
            for (k, a, b) in ts {
                let ca = go(
                    nodes,
                    rc,
                    k_index,
                    *a,
                    depth - 1,
                    false,
                    tnodes,
                    leaves,
                    tmap,
                    memo,
                );
                let cb = go(
                    nodes,
                    rc,
                    k_index,
                    *b,
                    depth - 1,
                    false,
                    tnodes,
                    leaves,
                    tmap,
                    memo,
                );
                terms.push((k_index(k), ca, cb));
            }
            tnodes.push(TemplateNode::Sum(terms));
            tmap.push(u32::try_from(n).expect("node index fits in u32"));
            u32::try_from(tnodes.len() - 1).expect("template node fits in u32")
        } else {
            let hole = u32::try_from(leaves.len()).expect("leaf count fits in u32");
            leaves.push(u32::try_from(n).expect("node index fits in u32"));
            tnodes.push(TemplateNode::Leaf(hole));
            tmap.push(u32::try_from(n).expect("node index fits in u32"));
            u32::try_from(tnodes.len() - 1).expect("template node fits in u32")
        };
        memo.insert((n, depth), idx);
        idx
    }

    go(
        nodes,
        rc,
        k_index,
        root,
        TEMPLATE_DEPTH,
        true,
        &mut tnodes,
        &mut leaves,
        &mut tmap,
        &mut memo,
    );
    let nleaves = leaves.len();
    (
        Template {
            nodes: tnodes,
            nleaves,
        },
        tmap,
    )
}

/// Records the input-position -> name correspondence *as wires are allocated*.
///
/// The input layout is the one place where the meaning of a proved theorem is
/// chosen rather than checked: nothing downstream can tell `pk_x` from `r`.
/// Recording it at the point of allocation keeps it honest — the builder is
/// what advances `pos`, so a name cannot drift from the position it labels.
///
/// Position 0 is the reserved constant `one`
/// (`compile_logic::K_FIRST_WIRE_POSITION == 1`), recorded by [`LayoutBuilder::new`].
#[derive(Debug, Default)]
pub struct LayoutBuilder {
    entries: Vec<(usize, String)>,
}

impl LayoutBuilder {
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: vec![(0, "one".to_string())],
        }
    }

    /// Allocates the next input wire and records `name` for its position.
    pub fn next<L: compile_logic::LogicIO>(
        &mut self,
        io: &L,
        pos: &mut usize,
        name: impl Into<String>,
    ) -> L::Wire {
        let p = *pos;
        let wire = io.next(pos);
        self.entries.push((p, name.into()));
        wire
    }

    /// Records one already-allocated position under exactly `name`.
    ///
    /// Like [`LayoutBuilder::record_range`] this does not allocate: read the position back off
    /// the wire the circuit's own allocator produced. Use this for scalar inputs, where
    /// `record_range`'s `name_0` suffix would be noise.
    pub fn record(&mut self, position: usize, name: impl Into<String>) {
        self.entries.push((position, name.into()));
    }

    /// Records `count` consecutive positions starting at `start`, as `name_0 … name_{count-1}`.
    ///
    /// Unlike [`LayoutBuilder::next`] this does not allocate.  Use it for wires allocated by a
    /// circuit's own allocator — bit-vector inputs, where one logical value spans 32 positions
    /// — and read each group's base position back off the allocated value
    /// (`BitvecIO::position_in_input_array`).  The name is then attached to the position the
    /// circuit actually used, rather than to a re-derivation of the allocation order in the
    /// caller, which is the thing that would silently drift.
    pub fn record_range(&mut self, start: usize, count: usize, name: &str) {
        for i in 0..count {
            self.entries.push((start + i, format!("{name}_{i}")));
        }
    }

    /// Layout entries in the form [`build_sidecar`] consumes.
    #[must_use]
    pub fn entries(&self) -> Vec<InputLayoutEntry<'_>> {
        self.entries
            .iter()
            .map(|(position, name)| InputLayoutEntry {
                position: *position,
                name,
            })
            .collect()
    }

    /// Panics unless every input position below `ninput` carries a name. A
    /// partial layout is not unsound — an unnamed position simply cannot be
    /// referred to by the spec bridge — but a complete one is reviewable.
    pub fn assert_covers(&self, ninput: usize) {
        let mut seen: Vec<Option<&str>> = vec![None; ninput];
        for (p, name) in &self.entries {
            assert!(*p < ninput, "layout position {p} out of range");
            // Two names for one position is a layout bug: the spec bridge would then have two
            // aliases for the same wire, one of which is certainly mislabelled.
            assert!(
                seen[*p].is_none_or(|prior| prior == name),
                "layout position {p} named twice: {:?} and {name:?}",
                seen[*p]
            );
            seen[*p] = Some(name);
        }
        let mut seen: Vec<bool> = seen.into_iter().map(|entry| entry.is_some()).collect();
        seen.truncate(ninput);
        let missing: Vec<usize> = (0..ninput).filter(|i| !seen[*i]).collect();
        assert!(
            missing.is_empty(),
            "input layout misses positions {missing:?}"
        );
    }
}

/// Builds the certificate sidecar for a compiled circuit.
///
/// Panics if the sidecar cannot be verified against the circuit itself:
/// id mismatch, DAG + wire map failing to reproduce the circuit terms,
/// assertion records disagreeing with the debug symbols, or malformed input
/// layout.
#[must_use]
pub fn build_sidecar<F: CompileField>(
    f: &F,
    field_id: FieldID,
    circuit: &Circuit<F>,
    symbols: &CircuitDebugSymbols,
    info: &ScheduleInfo<F>,
    input_layout: &[InputLayoutEntry<'_>],
) -> Vec<u8> {
    let raw = &circuit.raw;

    // The pinned identity of the shipped circuit.
    assert_eq!(
        compute_id(f, raw),
        circuit.id,
        "circuit id does not match its contents"
    );

    let nlayers = raw.layers.len();
    assert_eq!(info.nlayers, nlayers, "layer count mismatch");
    assert_eq!(
        info.nodes.len(),
        info.node_wires.len(),
        "wire map does not cover all DAG nodes"
    );

    // Constant table lookup by canonical byte encoding.
    let mut const_index: rustc_hash::FxHashMap<Vec<u8>, u32> = rustc_hash::FxHashMap::default();
    for (i, c) in raw.constants.iter().enumerate() {
        let prev = const_index.insert(f.to_bytes(c), i as u32);
        assert!(prev.is_none(), "duplicate constant in constants table");
    }
    let k_index = |k: &F::E| -> u32 {
        *const_index
            .get(&f.to_bytes(k))
            .expect("term constant missing from constants table")
    };

    // The circuit's own expanded terms, per layer, in canonical order.
    let circuit_terms: Vec<Vec<Term<F>>> = raw
        .layers
        .iter()
        .map(|layer| layer.terms(&raw.constants))
        .collect();

    // The central self-check: the DAG plus the wire map must reproduce the
    // shipped circuit term for term. A sidecar that fails this check cannot
    // be built at all.
    check_dag_reproduces_circuit(f, info, &circuit_terms, &k_index, nlayers);

    // Assertion records must agree with the debug symbols.
    assert_eq!(
        info.assertions.len(),
        symbols.assertion_count(),
        "assertion record count does not match debug symbols"
    );
    for rec in &info.assertions {
        let sym_id = symbols
            .get_id(&rec.wire)
            .unwrap_or_else(|| panic!("no debug symbol for assertion wire {:?}", rec.wire));
        assert_eq!(
            symbols.tracker().find(sym_id),
            symbols.tracker().find(rec.id),
            "assertion identity mismatch at wire {:?}",
            rec.wire
        );
    }

    // Input layout validation.
    let mut seen = vec![false; raw.ninput];
    for entry in input_layout {
        assert!(
            entry.position < raw.ninput,
            "input layout position {} out of range (ninput = {})",
            entry.position,
            raw.ninput
        );
        assert!(
            !seen[entry.position],
            "duplicate input layout position {}",
            entry.position
        );
        seen[entry.position] = true;
    }

    serialize(
        f,
        field_id,
        circuit,
        symbols,
        info,
        (&circuit_terms, &k_index),
        input_layout,
    )
}

/// Wire coordinates of a DAG node operand, checked to sit exactly one layer
/// below the consumer (with the input pseudo-layer `nlayers` below the
/// deepest circuit layer).
fn operand_wire<F: CompileField>(
    info: &ScheduleInfo<F>,
    node_idx: usize,
    consumer_layer: usize,
) -> usize {
    let wire =
        info.node_wires[node_idx].unwrap_or_else(|| panic!("operand node {node_idx} has no wire"));
    assert_eq!(
        wire.layer,
        consumer_layer + 1,
        "operand node {node_idx} is not in the layer below its consumer"
    );
    wire.index
}

fn check_dag_reproduces_circuit<F: CompileField>(
    f: &F,
    info: &ScheduleInfo<F>,
    circuit_terms: &[Vec<Term<F>>],
    k_index: &impl Fn(&F::E) -> u32,
    nlayers: usize,
) {
    let mut dag_terms: Vec<Vec<Term<F>>> = vec![Vec::new(); nlayers];
    for (i, node) in info.nodes.iter().enumerate() {
        let WExpr::Sum(terms) = node else { continue };
        let wire = info.node_wires[i]
            .as_ref()
            .unwrap_or_else(|| panic!("sum node {i} has no wire"));
        assert!(
            wire.layer < nlayers,
            "sum node {i} wire outside the circuit layers"
        );
        for (k, w0, w1) in terms {
            let p0 = operand_wire(info, *w0, wire.layer);
            let p1 = operand_wire(info, *w1, wire.layer);
            let (h0, h1) = if p1 < p0 { (p1, p0) } else { (p0, p1) };
            dag_terms[wire.layer].push(Term {
                k: k.clone(),
                g: u32::try_from(wire.index).expect("wire index fits in u32"),
                h0: u32::try_from(h0).expect("wire index fits in u32"),
                h1: u32::try_from(h1).expect("wire index fits in u32"),
            });
            // The constant must exist in the circuit's table.
            let _ = k_index(k);
        }
    }

    for (l, terms) in dag_terms.iter_mut().enumerate() {
        terms.sort_by(|a, b| compare_term(f, a, b));
        assert_eq!(
            terms.len(),
            circuit_terms[l].len(),
            "term count mismatch in layer {l}: dag has {}, circuit has {}",
            terms.len(),
            circuit_terms[l].len()
        );
        for (i, t) in terms.iter().enumerate() {
            assert!(
                t == &circuit_terms[l][i],
                "term mismatch in layer {l} at position {i}: dag {t:?} vs circuit {:?}",
                circuit_terms[l][i]
            );
        }
    }
}

fn serialize<F: CompileField>(
    f: &F,
    field_id: FieldID,
    circuit: &Circuit<F>,
    symbols: &CircuitDebugSymbols,
    info: &ScheduleInfo<F>,
    derived: (&[Vec<Term<F>>], &impl Fn(&F::E) -> u32),
    input_layout: &[InputLayoutEntry<'_>],
) -> Vec<u8> {
    let (circuit_terms, k_index) = derived;
    let raw = &circuit.raw;
    let mut out = Vec::new();

    out.extend_from_slice(&CERT_MAGIC);
    push_u32(&mut out, CERT_VERSION);
    push_u32(&mut out, field_id as u32);
    out.extend_from_slice(&circuit.id);
    push_u32(
        &mut out,
        u32::try_from(f.serialized_size_bytes()).expect("element size fits in u32"),
    );
    push_u64(&mut out, raw.ninput as u64);
    push_u64(&mut out, raw.npublic_input as u64);
    push_u64(&mut out, raw.noutput as u64);
    push_u64(&mut out, raw.logv as u64);
    push_u64(&mut out, raw.subfield_boundary as u64);

    push_u32(
        &mut out,
        u32::try_from(raw.constants.len()).expect("constant count fits in u32"),
    );
    for c in &raw.constants {
        out.extend_from_slice(&f.to_bytes(c));
    }

    push_u32(
        &mut out,
        u32::try_from(raw.layers.len()).expect("layer count fits in u32"),
    );
    for (l, layer) in raw.layers.iter().enumerate() {
        push_u64(&mut out, layer.nw() as u64);
        push_u64(&mut out, layer.logw() as u64);
        push_u64(&mut out, circuit_terms[l].len() as u64);
        for t in &circuit_terms[l] {
            push_u32(&mut out, t.g);
            push_u32(&mut out, t.h0);
            push_u32(&mut out, t.h1);
            push_u32(&mut out, k_index(&t.k));
        }
    }

    push_u64(&mut out, info.nodes.len() as u64);
    for node in &info.nodes {
        match node {
            WExpr::Unspecified => panic!("Unspecified node in circuit DAG"),
            WExpr::Input {
                position_in_input_array,
            } => {
                out.push(TAG_INPUT);
                push_u32(
                    &mut out,
                    u32::try_from(*position_in_input_array).expect("input position fits in u32"),
                );
            }
            WExpr::Sum(terms) => {
                out.push(TAG_SUM);
                push_u32(
                    &mut out,
                    u32::try_from(terms.len()).expect("term count fits in u32"),
                );
                for (k, w0, w1) in terms {
                    push_u32(&mut out, k_index(k));
                    push_u32(
                        &mut out,
                        u32::try_from(*w0).expect("node index fits in u32"),
                    );
                    push_u32(
                        &mut out,
                        u32::try_from(*w1).expect("node index fits in u32"),
                    );
                }
            }
            WExpr::Assert0(w) => {
                out.push(TAG_ASSERT0);
                push_u32(&mut out, u32::try_from(*w).expect("node index fits in u32"));
            }
        }
    }

    for wire in &info.node_wires {
        match wire {
            Some(w) => {
                out.push(1);
                push_u32(&mut out, u32::try_from(w.layer).expect("layer fits in u32"));
                push_u32(
                    &mut out,
                    u32::try_from(w.index).expect("wire index fits in u32"),
                );
            }
            None => out.push(0),
        }
    }

    // Templates: one shape per distinct asserted sub-DAG, with each assertion recording
    // which template it instantiates and what fills the holes.
    let rc = refcounts(&info.nodes);
    let mut templates: Vec<Template> = Vec::new();
    let mut tindex: rustc_hash::FxHashMap<Template, u32> = rustc_hash::FxHashMap::default();
    let mut inst: rustc_hash::FxHashMap<u32, (u32, Vec<u32>)> = rustc_hash::FxHashMap::default();
    for rec in &info.assertions {
        let (t, mapping) = extract_template(&info.nodes, &rc, &k_index, rec.asserted_node as usize);
        let id = *tindex.entry(t.clone()).or_insert_with(|| {
            templates.push(t);
            u32::try_from(templates.len() - 1).expect("template count fits in u32")
        });
        inst.insert(rec.asserted_node, (id, mapping));
    }

    let mut assertions: Vec<_> = info.assertions.iter().collect();
    assertions.sort_by_key(|rec| (rec.wire.layer, rec.wire.index));
    push_u32(
        &mut out,
        u32::try_from(assertions.len()).expect("assertion count fits in u32"),
    );
    for rec in assertions {
        push_u32(&mut out, rec.assert_node);
        push_u32(&mut out, rec.asserted_node);
        push_u32(
            &mut out,
            u32::try_from(rec.wire.layer).expect("layer fits in u32"),
        );
        push_u32(
            &mut out,
            u32::try_from(rec.wire.index).expect("wire index fits in u32"),
        );
        // All scope paths satisfied by this assertion identity, including the
        // paths of source-level assertions merged with it by CSE/dedup.
        let paths = symbols.tracker().group_paths(rec.id);
        push_u32(
            &mut out,
            u32::try_from(paths.len()).expect("path count fits in u32"),
        );
        for p in &paths {
            push_str(&mut out, p);
        }
        let (tid, mapping) = &inst[&rec.asserted_node];
        push_u32(&mut out, *tid);
        push_u32(
            &mut out,
            u32::try_from(mapping.len()).expect("mapping fits in u32"),
        );
        for l in mapping {
            push_u32(&mut out, *l);
        }
    }

    push_u32(
        &mut out,
        u32::try_from(templates.len()).expect("template count fits in u32"),
    );
    for t in &templates {
        push_u32(
            &mut out,
            u32::try_from(t.nodes.len()).expect("template size fits in u32"),
        );
        push_u32(
            &mut out,
            u32::try_from(t.nleaves).expect("leaf count fits in u32"),
        );
        for nd in &t.nodes {
            match nd {
                TemplateNode::Leaf(h) => {
                    out.push(0);
                    push_u32(&mut out, *h);
                }
                TemplateNode::Sum(ts) => {
                    out.push(1);
                    push_u32(
                        &mut out,
                        u32::try_from(ts.len()).expect("term count fits in u32"),
                    );
                    for (k, a, b) in ts {
                        push_u32(&mut out, *k);
                        push_u32(&mut out, *a);
                        push_u32(&mut out, *b);
                    }
                }
            }
        }
    }

    push_u32(
        &mut out,
        u32::try_from(input_layout.len()).expect("layout count fits in u32"),
    );
    for entry in input_layout {
        push_u32(
            &mut out,
            u32::try_from(entry.position).expect("input position fits in u32"),
        );
        push_str(&mut out, entry.name);
    }

    out.extend_from_slice(&CERT_MAGIC);
    out
}

fn push_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn push_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn push_str(out: &mut Vec<u8>, s: &str) {
    push_u32(
        out,
        u32::try_from(s.len()).expect("string length fits in u32"),
    );
    out.extend_from_slice(s.as_bytes());
}

// =============================================================================
// Parsing
// =============================================================================

/// A parsed layer: wire count, log width, and expanded canonical terms
/// `(g, h0, h1, k_index)`.
#[derive(Debug, Clone)]
pub struct ParsedLayer {
    pub nw: usize,
    pub logw: usize,
    pub terms: Vec<(u32, u32, u32, u32)>,
}

/// A parsed DAG node.
#[derive(Debug, Clone)]
pub enum ParsedNode {
    Input { position: usize },
    Sum { terms: Vec<(u32, usize, usize)> },
    Assert0 { w: usize },
}

/// A parsed assertion record.
#[derive(Debug, Clone)]
pub struct ParsedAssertion {
    pub assert_node: usize,
    pub asserted_node: usize,
    pub wire_layer: usize,
    pub wire_index: usize,
    pub paths: Vec<String>,
    /// Which template this assertion instantiates, and the DAG node for each template node.
    pub template: usize,
    pub mapping: Vec<usize>,
}

/// The parsed certificate sidecar. Field element constants are held as their
/// canonical byte encodings; use the circuit's field to interpret them.
#[derive(Debug, Clone)]
pub struct ParsedSidecar {
    pub version: u32,
    pub field_id: u32,
    pub id: [u8; 32],
    pub elt_size: usize,
    pub ninput: usize,
    pub npublic_input: usize,
    pub noutput: usize,
    pub logv: usize,
    pub subfield_boundary: usize,
    pub constants: Vec<Vec<u8>>,
    pub layers: Vec<ParsedLayer>,
    pub nodes: Vec<ParsedNode>,
    /// Wire coordinates per node index; input nodes sit at the pseudo-layer
    /// `layers.len()`.
    pub node_wires: Vec<Option<(usize, usize)>>,
    pub assertions: Vec<ParsedAssertion>,
    pub input_layout: Vec<(usize, String)>,
    /// Distinct assertion shapes; assertions index into this.
    pub templates: Vec<Template>,
}

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.pos + n > self.buf.len() {
            return Err(format!(
                "sidecar truncated: need {n} bytes at offset {}, have {}",
                self.pos,
                self.buf.len() - self.pos
            ));
        }
        let slice = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, String> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn u64(&mut self) -> Result<u64, String> {
        let b = self.take(8)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    fn usize32(&mut self) -> Result<usize, String> {
        self.u32().map(|v| v as usize)
    }

    fn usize64(&mut self) -> Result<usize, String> {
        self.u64().map(|v| v as usize)
    }

    fn string(&mut self) -> Result<String, String> {
        let len = self.usize32()?;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|e| format!("invalid utf8: {e}"))
    }
}

/// Parses and structurally validates a certificate sidecar.
pub fn parse_sidecar(bytes: &[u8]) -> Result<ParsedSidecar, String> {
    let mut r = Reader::new(bytes);

    let magic = r.take(8)?;
    if magic != CERT_MAGIC {
        return Err("bad sidecar magic".to_string());
    }
    let version = r.u32()?;
    if version != CERT_VERSION {
        return Err(format!("unsupported sidecar version {version}"));
    }
    let field_id = r.u32()?;
    let id_bytes = r.take(32)?;
    let mut id = [0u8; 32];
    id.copy_from_slice(id_bytes);
    let elt_size = r.usize32()?;
    if elt_size == 0 {
        return Err("element size must be non-zero".to_string());
    }
    let ninput = r.usize64()?;
    let npublic_input = r.usize64()?;
    let noutput = r.usize64()?;
    let logv = r.usize64()?;
    let subfield_boundary = r.usize64()?;

    let nconstants = r.usize32()?;
    let mut constants = Vec::with_capacity(nconstants);
    for _ in 0..nconstants {
        constants.push(r.take(elt_size)?.to_vec());
    }

    let nlayers = r.usize32()?;
    let mut layers = Vec::with_capacity(nlayers);
    for _ in 0..nlayers {
        let nw = r.usize64()?;
        let logw = r.usize64()?;
        let nterms = r.usize64()?;
        let mut terms = Vec::with_capacity(nterms);
        for _ in 0..nterms {
            let g = r.u32()?;
            let h0 = r.u32()?;
            let h1 = r.u32()?;
            let k_index = r.u32()?;
            if k_index as usize >= nconstants {
                return Err(format!("term constant index {k_index} out of range"));
            }
            if h0 > h1 {
                return Err(format!("term ({g}, {h0}, {h1}) is not canonical"));
            }
            terms.push((g, h0, h1, k_index));
        }
        layers.push(ParsedLayer { nw, logw, terms });
    }

    let nnodes = r.usize64()?;
    let mut nodes = Vec::with_capacity(nnodes);
    for _ in 0..nnodes {
        let tag = r.u8()?;
        match tag {
            TAG_INPUT => {
                let position = r.usize32()?;
                if position >= ninput {
                    return Err(format!("input position {position} out of range"));
                }
                nodes.push(ParsedNode::Input { position });
            }
            TAG_SUM => {
                let nterms = r.usize32()?;
                let mut terms = Vec::with_capacity(nterms);
                for _ in 0..nterms {
                    let k_index = r.u32()?;
                    let w0 = r.usize32()?;
                    let w1 = r.usize32()?;
                    if k_index as usize >= nconstants {
                        return Err(format!("dag constant index {k_index} out of range"));
                    }
                    terms.push((k_index, w0, w1));
                }
                nodes.push(ParsedNode::Sum { terms });
            }
            TAG_ASSERT0 => {
                let w = r.usize32()?;
                nodes.push(ParsedNode::Assert0 { w });
            }
            _ => return Err(format!("unknown node tag {tag}")),
        }
    }

    let mut node_wires = Vec::with_capacity(nnodes);
    for _ in 0..nnodes {
        let present = r.u8()?;
        match present {
            0 => node_wires.push(None),
            1 => {
                let layer = r.usize32()?;
                let index = r.usize32()?;
                if layer > nlayers {
                    return Err(format!("wire layer {layer} out of range"));
                }
                node_wires.push(Some((layer, index)));
            }
            _ => return Err(format!("invalid wire-present byte {present}")),
        }
    }

    // Node index bounds for DAG references.
    for (i, node) in nodes.iter().enumerate() {
        match node {
            ParsedNode::Sum { terms } => {
                for (_, w0, w1) in terms {
                    if *w0 >= nnodes || *w1 >= nnodes {
                        return Err(format!("node {i} references out-of-range operand"));
                    }
                }
            }
            ParsedNode::Assert0 { w } => {
                if *w >= nnodes {
                    return Err(format!("assertion node {i} references out-of-range node"));
                }
            }
            ParsedNode::Input { .. } => {}
        }
    }

    let nassertions = r.usize32()?;
    let mut assertions = Vec::with_capacity(nassertions);
    for _ in 0..nassertions {
        let assert_node = r.usize32()?;
        let asserted_node = r.usize32()?;
        let wire_layer = r.usize32()?;
        let wire_index = r.usize32()?;
        let npaths = r.usize32()?;
        let mut paths = Vec::with_capacity(npaths);
        for _ in 0..npaths {
            paths.push(r.string()?);
        }
        if assert_node >= nnodes || asserted_node >= nnodes {
            return Err("assertion record references out-of-range node".to_string());
        }
        let template = r.usize32()?;
        let nmap = r.usize32()?;
        let mut mapping = Vec::with_capacity(nmap);
        for _ in 0..nmap {
            let l = r.usize32()?;
            if l >= nnodes {
                return Err("template mapping out of range".to_string());
            }
            mapping.push(l);
        }
        assertions.push(ParsedAssertion {
            assert_node,
            asserted_node,
            wire_layer,
            wire_index,
            paths,
            template,
            mapping,
        });
    }

    let ntemplates = r.usize32()?;
    let mut templates = Vec::with_capacity(ntemplates);
    for _ in 0..ntemplates {
        let nn = r.usize32()?;
        let nleaves = r.usize32()?;
        let mut nodes = Vec::with_capacity(nn);
        for _ in 0..nn {
            match r.u8()? {
                0 => nodes.push(TemplateNode::Leaf(r.u32()?)),
                1 => {
                    let nt = r.usize32()?;
                    let mut ts = Vec::with_capacity(nt);
                    for _ in 0..nt {
                        ts.push((r.u32()?, r.u32()?, r.u32()?));
                    }
                    nodes.push(TemplateNode::Sum(ts));
                }
                t => return Err(format!("unknown template node tag {t}")),
            }
        }
        templates.push(Template { nodes, nleaves });
    }
    for a in &assertions {
        if a.template >= ntemplates {
            return Err("assertion references unknown template".to_string());
        }
    }

    let nlayout = r.usize32()?;
    let mut input_layout = Vec::with_capacity(nlayout);
    let mut seen = vec![false; ninput];
    for _ in 0..nlayout {
        let position = r.usize32()?;
        let name = r.string()?;
        if position >= ninput {
            return Err(format!("layout position {position} out of range"));
        }
        if seen[position] {
            return Err(format!("duplicate layout position {position}"));
        }
        seen[position] = true;
        input_layout.push((position, name));
    }

    let tail = r.take(8)?;
    if tail != CERT_MAGIC {
        return Err("bad trailing sidecar magic".to_string());
    }

    Ok(ParsedSidecar {
        version,
        field_id,
        id,
        elt_size,
        ninput,
        npublic_input,
        noutput,
        logv,
        subfield_boundary,
        constants,
        layers,
        nodes,
        node_wires,
        assertions,
        input_layout,
        templates,
    })
}

impl ParsedSidecar {
    /// Recomputes the canonical circuit id from the parsed sidecar contents.
    /// If it matches the stored `id` (and hence the production artifact's
    /// id), the sidecar's expanded terms fully determine the shipped circuit.
    pub fn recompute_id<F: SerializableField>(&self, f: &F) -> Result<[u8; 32], String> {
        if self.elt_size != f.serialized_size_bytes() {
            return Err(format!(
                "field element size mismatch: sidecar {} vs field {}",
                self.elt_size,
                f.serialized_size_bytes()
            ));
        }
        let mut layers = Vec::with_capacity(self.layers.len());
        for layer in &self.layers {
            let mut terms: Vec<(u32, u32, u32, u32)> = layer.terms.clone();
            terms.sort_by(|a, b| {
                ::util::morton::cmp(a.1 as usize, a.2 as usize, b.1 as usize, b.2 as usize)
                    .then(a.0.cmp(&b.0))
                    .then_with(|| self.constants[a.3 as usize].cmp(&self.constants[b.3 as usize]))
            });
            let mut deltas = Vec::with_capacity(terms.len());
            let mut prev_g = 0u32;
            let mut prev_h0 = 0u32;
            let mut prev_h1 = 0u32;
            for (g, h0, h1, k_index) in terms {
                deltas.push(TermDelta {
                    g: g.wrapping_sub(prev_g),
                    h: [h0.wrapping_sub(prev_h0), h1.wrapping_sub(prev_h1)],
                    k_index,
                });
                prev_g = g;
                prev_h0 = h0;
                prev_h1 = h1;
            }
            let seq: Vec<u32> = (0..deltas.len() as u32).collect();
            layers.push(Layer::new(layer.nw, layer.logw, deltas, vec![seq], vec![0]));
        }

        let mut constants = Vec::with_capacity(self.constants.len());
        for c in &self.constants {
            constants.push(f.bytes_to_element(c)?);
        }

        let raw = RawCircuit {
            ninput: self.ninput,
            npublic_input: self.npublic_input,
            noutput: self.noutput,
            logv: self.logv,
            subfield_boundary: self.subfield_boundary,
            constants,
            layers,
        };
        Ok(compute_id(f, &raw))
    }
}

// =============================================================================
// Lean emission
// =============================================================================

/// Options for [`emit_lean`].
#[derive(Debug, Clone, Copy)]
pub struct EmitOptions<'a> {
    /// Base name of the generated modules, e.g. `"Rung1"`. Modules are emitted as
    /// `quadcert.<name>Chunk0`, ..., `quadcert.<name>Data`.
    pub name: &'a str,
    /// Maximum list elements per chunk module. `0` emits a single module.
    ///
    /// Measured on this toolchain: elaboration costs roughly 40 KB resident per list
    /// element, a 48k-element literal needs 4.1 GB and exceeds the default heartbeat
    /// limit, and chunks of 750–3000 keep peak resident memory at 300–600 MB
    /// regardless of total size. 2000 is a reasonable default.
    pub chunk: usize,
    /// Base name of the `lfc3_to_lean` modules for the **same** circuit, e.g. `"Sha256Blk"`.
    ///
    /// When set, the layer terms are not re-emitted as a sidecar-owned copy: `raw.layers`
    /// points at the artifact's own `allTerms_{l}`, and `Data` gains `advice`, `artifactRaw`
    /// and `artifactRaw_eq_raw`.
    ///
    /// Sharing rather than duplicating is deliberate.  The sidecar's term list is pure
    /// redundancy — the artifact owns the terms — so proving a duplicate copy equal to the
    /// decoded one is work that only exists because the duplicate does.  Sharing deletes the
    /// obligation instead of discharging it, halves the generated bytes, and leaves
    /// `artifactRaw_eq_raw` a cheap `rfl` rather than a structural comparison of two
    /// hundred-thousand-element literals.  What that `rfl` still checks is everything the
    /// sidecar *does* claim independently: the dimensions, `logv`, `subfieldBoundary`, the
    /// constant count and every layer's `nw`.
    pub artifact: Option<&'a str>,
}

/// Emits Lean data modules for a parsed sidecar.
///
/// Module layout (all import `quadcert.Core.Raw` only — never Mathlib):
///
/// * `<name>Wire{k}`  — pieces of the wire map, as balanced if-trees;
/// * `<name>Base`     — the `wireFn` dispatcher and `nlayers`;
/// * `<name>Terms{l}_{j}` — layer-term list chunks;
/// * `<name>Nodes{k}` — node list chunks, **each proving its own slice of the structural
///   check** with `by decide`;
/// * `<name>Data`     — assembles `raw` and composes the slices into `raw.ok = true`.
///
/// Chunking the *check*, not just the data, is the point. A whole-circuit `decide` must
/// reduce every node and term in one kernel computation; measured on ECDSA2 that needs
/// over 40 GB and still times out. A per-chunk `decide` reduces only that chunk.
#[must_use]
pub fn emit_lean(s: &ParsedSidecar, opts: &EmitOptions<'_>) -> Vec<(String, String)> {
    let name = opts.name;
    let chunk = if opts.chunk == 0 {
        usize::MAX
    } else {
        opts.chunk
    };
    let nnodes = s.nodes.len();
    let nlayers = s.layers.len();
    let mut out = Vec::new();
    let hdr = |extra: &str| {
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Core.Raw\n{extra}\
             set_option maxRecDepth 4000000\n\
             set_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n"
        )
    };

    fn tree(w: &[Option<(usize, usize)>], lo: usize, hi: usize, base: usize) -> String {
        if hi - lo == 1 {
            return match w[lo - base] {
                Some((l, i)) => format!("some ({l}, {i})"),
                None => "none".to_string(),
            };
        }
        let mid = lo + (hi - lo) / 2;
        format!(
            "(if i < {mid} then {} else {})",
            tree(w, lo, mid, base),
            tree(w, mid, hi, base)
        )
    }
    let wstep = chunk.min(nnodes.max(1));
    let mut wire_mods = Vec::new();
    let mut dispatch = String::new();
    for (k, part) in s.node_wires.chunks(wstep).enumerate() {
        let lo = k * wstep;
        let hi = lo + part.len();
        let m = format!("{name}Wire{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "{}noncomputable def wireFn_{k} : Nat → Option (Nat × Nat) := fun i =>\n  {}\n\nend Quadcert.Gen.{name}\n",
                hdr(""),
                tree(part, lo, hi, lo)
            ),
        ));
        wire_mods.push(m);
        dispatch.push_str(&format!("if i < {hi} then wireFn_{k} i else "));
    }
    dispatch.push_str("none");
    // Outer guard: makes `wireFn_lt` a single `if_neg` instead of discharging one
    // `¬ i < k` per dispatch branch.
    let dispatch = format!("if i < {nnodes} then ({dispatch}) else none");

    let fallback = s
        .node_wires
        .iter()
        .position(std::option::Option::is_none)
        .unwrap_or(0);
    // `wireInv` as a bisection on the packed key `layer * stride + index`, **split across
    // modules** exactly like `wireFn`. A pattern match over every wire reduces in O(cases),
    // which makes `okInv` quadratic; and a single 27k-leaf definition exhausts memory during
    // elaboration even when its reduction is cheap.
    let stride = s
        .node_wires
        .iter()
        .filter_map(|w| w.map(|(_, g)| g))
        .max()
        .map_or(1, |m| m + 1);
    let mut keyed: Vec<(usize, usize)> = s
        .node_wires
        .iter()
        .enumerate()
        .filter_map(|(i, w)| w.map(|(l, g)| (l * stride + g, i)))
        .collect();
    keyed.sort_unstable();
    fn ktree(kv: &[(usize, usize)], fallback: usize) -> String {
        match kv.len() {
            0 => format!("{fallback}"),
            1 => format!("(if k == {} then {} else {fallback})", kv[0].0, kv[0].1),
            _ => {
                let mid = kv.len() / 2;
                format!(
                    "(if k < {} then {} else {})",
                    kv[mid].0,
                    ktree(&kv[..mid], fallback),
                    ktree(&kv[mid..], fallback)
                )
            }
        }
    }
    let istep = chunk.min(keyed.len().max(1));
    let mut inv_mods = Vec::new();
    let mut inv_dispatch = String::new();
    for (k, part) in keyed.chunks(istep).enumerate() {
        let m = format!("{name}Inv{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "{}def wireInvKey_{k} (k : Nat) : Nat :=\n  {}\n\nend Quadcert.Gen.{name}\n",
                hdr(""),
                ktree(part, fallback)
            ),
        ));
        inv_mods.push(m);
        // chunks are key-sorted, so dispatch on the first key of the next chunk
        let upper = keyed.get((k + 1) * istep).map_or(usize::MAX, |kv| kv.0);
        if upper == usize::MAX {
            inv_dispatch.push_str(&format!("wireInvKey_{k} k"));
        } else {
            inv_dispatch.push_str(&format!("if k < {upper} then wireInvKey_{k} k else "));
        }
    }
    if keyed.is_empty() {
        inv_dispatch.push_str(&format!("{fallback}"));
    }
    let inv = format!(
        "/-- Left inverse of the wire map, as a bisection on the packed key\n\
         `layer * {stride} + index`. -/\n\
         def wireInvKey (k : Nat) : Nat :=\n  {inv_dispatch}\n\n\
         def wireInv (p : Nat × Nat) : Nat := wireInvKey (p.1 * {stride} + p.2)\n"
    );

    // Constant table as canonical integers from the artifact's own encoding, so the spec
    // bridge *proves* the correspondence to `CurveParameters` rather than a human reading
    // it out of a comment.
    let mut consts_def = String::from(
        "/-- Canonical constant values, as hex integers from the artifact's encoding. -/\ndef constNat : Nat → Nat\n",
    );
    for (i, c) in s.constants.iter().enumerate() {
        let hex: String = c.iter().rev().map(|b| format!("{b:02x}")).collect();
        let t = hex.trim_start_matches('0');
        consts_def.push_str(&format!(
            "  | {i} => 0x{}\n",
            if t.is_empty() { "0" } else { t }
        ));
    }
    consts_def.push_str("  | _ => 0\n\n");
    // No field-valued table here: the generated modules are Mathlib-free by design, and
    // `Field` is not in scope. The spec module defines
    // `consts F : Nat → F := fun i => (constNat i : F)` from these integers.

    let inv_imports: String = inv_mods
        .iter()
        .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
        .collect();

    let wire_imports: String = wire_mods
        .iter()
        .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
        .collect();
    out.push((
        format!("Gen/{name}/{name}Base.lean"),
        format!(
            "{}noncomputable def wireFn : Nat → Option (Nat × Nat) := fun i =>\n  {dispatch}\n\n\
             abbrev nlayers : Nat := {nlayers}\n\n{inv}\n{consts_def}\nend Quadcert.Gen.{name}\n",
            hdr(&format!("{wire_imports}{inv_imports}"))
        ),
    ));

    let mut term_mods = Vec::new();
    let mut layer_defs = Vec::new();
    // The terms of each layer as a Lean expression, so the `sum_local` permutation modules can
    // name them without going through `raw` (which would drag in every other chunk).
    let mut layer_terms_expr: Vec<String> = Vec::new();
    for (l, ly) in s.layers.iter().enumerate() {
        // With an artifact, the terms live there and the sidecar copy is not emitted at all.
        if let Some(artifact) = opts.artifact {
            layer_defs.push(format!("⟨{}, Quadcert.Gen.{artifact}.allTerms_{l}⟩", ly.nw));
            layer_terms_expr.push(format!("Quadcert.Gen.{artifact}.allTerms_{l}"));
            term_mods.push(format!("{artifact}ExpandedLayer{l}"));
            continue;
        }
        let items: Vec<String> = ly
            .terms
            .iter()
            .map(|(g, h0, h1, k)| format!("⟨{g}, {h0}, {h1}, {k}⟩"))
            .collect();
        if items.len() <= chunk {
            layer_defs.push(format!("⟨{}, [{}]⟩", ly.nw, items.join(", ")));
            layer_terms_expr.push(format!("[{}]", items.join(", ")));
        } else {
            let mut names = Vec::new();
            for (j, part) in items.chunks(chunk).enumerate() {
                let m = format!("{name}Terms{l}_{j}");
                out.push((
                    format!("Gen/{name}/{m}.lean"),
                    format!(
                        "{}def layerTerms{l}_{j} : List RawTerm :=\n  [{}]\n\nend Quadcert.Gen.{name}\n",
                        hdr(""),
                        part.join(", ")
                    ),
                ));
                term_mods.push(m);
                names.push(format!("layerTerms{l}_{j}"));
            }
            layer_defs.push(format!("⟨{}, {}⟩", ly.nw, names.join(" ++ ")));
            layer_terms_expr.push(names.join(" ++ "));
        }
    }

    let node_items: Vec<String> = s
        .nodes
        .iter()
        .map(|n| match n {
            ParsedNode::Input { position } => format!(".input {position}"),
            ParsedNode::Sum { terms } => {
                let ts: Vec<String> = terms
                    .iter()
                    .map(|(k, w0, w1)| format!("({k}, {w0}, {w1})"))
                    .collect();
                format!(".sum [{}]", ts.join(", "))
            }
            ParsedNode::Assert0 { w } => format!(".assert0 {w}"),
        })
        .collect();
    let nstep = chunk.min(nnodes.max(1));
    let mut node_mods = Vec::new();
    let mut node_names = Vec::new();
    let mut ok_names = Vec::new();
    let mut inv_names = Vec::new();
    let mut ranges: Vec<String> = Vec::new();
    let mut len_names = Vec::new();
    for (k, part) in node_items.chunks(nstep).enumerate() {
        let off = k * nstep;
        let m = format!("{name}Nodes{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "{}def nodes_{k} : List RawNode :=\n  [{}]\n\n\
                 theorem len_{k} : nodes_{k}.length = {} := by rfl\n\n\
                 /-- This chunk's slice of the structural check. -/\n\
                 theorem ok_{k} :\n    \
                 ((nodes_{k}).zipIdx {off}).all (fun p => okNodeWith wireFn nlayers p.1 p.2)\n      \
                 = true := by decide +kernel\n\n\
                 /-- This chunk's slice of the inverse check. -/\n\
                 theorem inv_{k} : okInvRange wireFn wireInv {off} {len} = true := by decide +kernel\n\
                 \nend Quadcert.Gen.{name}\n",
                hdr(&format!("import quadcert.Gen.{name}.{name}Base\n")),
                part.join(", "),
                part.len(),
                len = part.len()
            ),
        ));
        node_mods.push(m);
        node_names.push(format!("nodes_{k}"));
        ok_names.push(format!("ok_{k}"));
        inv_names.push(format!("inv_{k}"));
        ranges.push(format!("({off}, {})", part.len()));
        len_names.push(format!("len_{k}"));
    }

    // Right-nested sum of chunk lengths: `okInvRange_split` needs the length in `a + b`
    // shape, and this is defeq to the literal total.
    let mut lensum = String::new();
    for (i, part) in node_items.chunks(nstep).enumerate() {
        if i + 1 == node_items.chunks(nstep).count() {
            lensum.push_str(&format!("{}", part.len()));
        } else {
            lensum.push_str(&format!("{} + (", part.len()));
        }
    }
    for i in 0..node_items.chunks(nstep).count().saturating_sub(1) {
        let _ = i;
        lensum.push(')');
    }

    // ---- sum_local certificates ----------------------------------------------
    //
    // `groupOf l g` is the layer's terms whose output wire is `g`, emitted as a bisection so
    // that instantiating `sum_local` at a node costs O(log nw) instead of a scan of the layer.
    // Three decidable checks on raw data make it sound (`Check.sum_local_of_raw`):
    //
    //   * `perm_l`  — the groups flatten to a permutation of the layer's own term list.  The
    //     witness is equal `msort` forms; `msort` is fuel-structural because `List.mergeSort`
    //     is well-founded and therefore does not reduce in the kernel at all.
    //   * `hom_l`   — every term in group `i` has `g = i`, over `List.range gbound`.
    //   * `corr_k`  — each node's group corresponds term-for-term to its own sum terms.
    //
    // The fuel and the comparison order are untrusted: `msort_perm` holds for any fuel and any
    // `le`, so wrong advice only makes the emitted equality fail to typecheck.
    // `L = 0 ∨ … ∨ L = nlayers-1`, and the matching `rcases` pattern. Substituting a literal
    // keeps every `groupOf L` / `azt L` reducible; a `match` on `L` would instead put the
    // symbolic `L` in the motive and drag the whole tree in with it.
    let disj = (0..nlayers)
        .map(|l| format!("L = {l}"))
        .collect::<Vec<_>>()
        .join(" ∨ ");
    let pats = (0..nlayers).map(|_| "rfl").collect::<Vec<_>>().join("|");
    let mut gbounds: Vec<usize> = Vec::new();
    let mut group_mods: Vec<String> = Vec::new();
    let mut group_def_mods: Vec<String> = Vec::new();
    let mut hom_arms = String::new();
    let mut perm_mods: Vec<String> = Vec::new();
    let mut perm_arms = String::new();

    fn gtree(groups: &[String], lo: usize, hi: usize, base: usize) -> String {
        if hi - lo == 1 {
            return groups[lo - base].clone();
        }
        let mid = lo + (hi - lo) / 2;
        format!(
            "(if i < {mid} then {} else {})",
            gtree(groups, lo, mid, base),
            gtree(groups, mid, hi, base)
        )
    }

    for (l, ly) in s.layers.iter().enumerate() {
        // `gbound` must cover every `g` the layer's terms mention *and* every wire index the
        // node map places on this layer, since `groupOkWith` checks `g < gbound L` there.
        let gbound = 1 + ly
            .terms
            .iter()
            .map(|t| t.0 as usize)
            .chain(
                s.node_wires
                    .iter()
                    .flatten()
                    .filter(|w| w.0 == l)
                    .map(|w| w.1),
            )
            .max()
            .unwrap_or(0);
        gbounds.push(gbound);

        // Group the layer's terms by output wire — **in the order the node that lives on that
        // wire lists them**, not in the layer's canonical order. `Raw.realisesAll` is positional,
        // and the two orders genuinely differ: the layer is sorted morton-on-(h0,h1)-then-g by
        // `assign_wire_ids`, while the DAG lists operands in evaluation order. Reordering a group
        // is free for the permutation (which is order-blind) and for homogeneity.
        let mut raw_groups: Vec<Vec<(u32, u32, u32, u32)>> = vec![Vec::new(); gbound];
        for t in &ly.terms {
            raw_groups[t.0 as usize].push(*t);
        }
        for (g, group) in raw_groups.iter_mut().enumerate() {
            // The sum node on this wire, if any.
            let Some(n) = s
                .node_wires
                .iter()
                .position(|w| *w == Some((l, g)))
            else {
                continue;
            };
            let ParsedNode::Sum { terms } = &s.nodes[n] else {
                continue;
            };
            if terms.len() != group.len() {
                // Not a reordering problem: the wire carries terms the node does not claim.
                continue;
            }
            let mut used = vec![false; group.len()];
            let mut ordered = Vec::with_capacity(group.len());
            for (k, w0, w1) in terms {
                let g0 = s.node_wires[*w0].map(|w| w.1);
                let g1 = s.node_wires[*w1].map(|w| w.1);
                let found = group.iter().enumerate().position(|(i, t)| {
                    !used[i]
                        && t.3 == *k
                        && ((g0 == Some(t.1 as usize) && g1 == Some(t.2 as usize))
                            || (g0 == Some(t.2 as usize) && g1 == Some(t.1 as usize)))
                });
                match found {
                    Some(i) => {
                        used[i] = true;
                        ordered.push(group[i]);
                    }
                    None => panic!(
                        "layer {l} wire {g}: node {n}'s sum term ({k}, {w0}, {w1}) is realised by \
                         no term of the wire's group; the DAG and the deployed layer disagree"
                    ),
                }
            }
            *group = ordered;
        }
        let groups: Vec<Vec<String>> = raw_groups
            .iter()
            .map(|ts| {
                ts.iter()
                    .map(|(g, h0, h1, k)| format!("⟨{g}, {h0}, {h1}, {k}⟩"))
                    .collect()
            })
            .collect();
        let leaves: Vec<String> = groups
            .iter()
            .map(|ts| format!("[{}]", ts.join(", ")))
            .collect();

        let gstep = chunk.min(gbound.max(1));
        let mut dispatch = String::new();
        let mut chunk_mods: Vec<String> = Vec::new();
        for (j, part) in leaves.chunks(gstep).enumerate() {
            let lo = j * gstep;
            let hi = lo + part.len();
            let m = format!("{name}Group{l}_{j}");
            out.push((
                format!("Gen/{name}/{m}.lean"),
                format!(
                    "{}def groupTree_{l}_{j} : Nat → List RawTerm := fun i =>\n  {}\n\n\
                     end Quadcert.Gen.{name}\n",
                    hdr(""),
                    gtree(part, lo, hi, lo)
                ),
            ));
            group_mods.push(m.clone());
            chunk_mods.push(m);
            dispatch.push_str(&format!("if i < {hi} then groupTree_{l}_{j} i else "));
        }
        dispatch.push_str("[]");

        // One module per layer. `homb_l` costs about 1.5 GB on ECDSA2's widest layers, and the
        // kernel retains each one for the rest of the module, so eleven of them in a single file
        // exceeds any workable cap — measured 5.7 GB before it gave up. In isolation each fits
        // comfortably. Outer guard on `gbound`, so `guard_l` is one `if_neg` and not one per
        // branch.
        let gm = format!("{name}GroupDef{l}");
        out.push((
            format!("Gen/{name}/{gm}.lean"),
            format!(
                "{}def groupOf_{l} : Nat → List RawTerm := fun i =>\n  \
                 if i < {gbound} then ({dispatch}) else []\n\n\
                 theorem guard_{l} : ∀ i, {gbound} ≤ i → groupOf_{l} i = [] := by\n  \
                 intro i h\n  simp only [groupOf_{l}]\n  rw [if_neg (by omega)]\n\n\
                 theorem homb_{l} :\n    \
                 (List.range {gbound}).all (fun i => (groupOf_{l} i).all (fun t => t.g == i))\n      \
                 = true := by decide +kernel\n\n\
                 theorem hom_{l} : ∀ i, ∀ t ∈ groupOf_{l} i, t.g = i :=\n  \
                 hom_of_bounded groupOf_{l} {gbound} guard_{l} homb_{l}\n\n\
                 end Quadcert.Gen.{name}\n",
                hdr(&chunk_mods
                    .iter()
                    .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                    .collect::<String>())
            ),
        ));
        group_def_mods.push(gm);
        hom_arms.push_str(&format!("  · exact hom_{l} i t ht\n"));

        // Fuel for `msort`: `n` covers both the merges (which need `n`) and the passes (which
        // need ceil(log2 n)). Too little only makes the equality fail, so it is untrusted.
        //
        // `decide +kernel` rather than `rfl`: `rfl` makes the *elaborator* do the reduction
        // with `isDefEq`, which is far slower than kernel whnf, and it duplicates the work the
        // kernel then repeats. `+kernel` hands the whole computation to the kernel once.
        let n = ly.terms.len().max(1);
        let fuel = n;
        // One `msort` per *block* of the group range, not one per layer.
        //
        // Sorting the whole layer does not survive SHA-256: layer 4 is 26,089 terms and costs
        // 175 s / 18.2 GB before aborting at the 16 GB cap, and a sort does not split along
        // ranges the way a `flatMap` does. Tiling the group range does split it -- the grouped
        // side cuts the range, the term side filters on the same bound -- and each block is then
        // an independent small sort. `PermBlocks.perm_of_blocks` reassembles them.
        //
        // This is also why no `{name}Flat{l}` is emitted any more: `groupFlat_{l}` existed only
        // to feed the whole-layer sort, and its literal was itself over the cap on layer 5.
        //
        // Blocks are sized by TERM COUNT, not group count. Density is very uneven -- layer 4's
        // seven 1000-group windows hold 1714, 4060, 2378, 1000, 4808, 7496 and 4633 terms -- and
        // cost tracks terms. At a 4,000-term target layer 4 takes 7 blocks (worst 4,128 terms,
        // 141 s / 5.9 GB for the module) and layer 5 takes 22 (worst 4,219, 34 s / 7.4 GB each);
        // small layers collapse to a single block, which is the old shape minus the sort.
        const BLOCK_TERMS: usize = 4000;
        let mut blocks: Vec<(usize, usize, usize)> = Vec::new();
        let (mut blo, mut run) = (0usize, 0usize);
        for g in 0..gbound {
            run += raw_groups[g].len();
            if run >= BLOCK_TERMS {
                blocks.push((blo, g + 1 - blo, run));
                blo = g + 1;
                run = 0;
            }
        }
        if blo < gbound || blocks.is_empty() {
            blocks.push((blo, gbound - blo, run));
        }
        debug_assert_eq!(blocks.iter().map(|b| b.1).sum::<usize>(), gbound);

        // The filter has to be distributed over the layer's chunk appends before any `decide`:
        // the kernel will not materialise layer 5's 89,048 terms as one list (even
        // `allTerms_5.length = 89048` is over the cap), but it filters them chunkwise in 8 s.
        // Same idiom as `filt_{l}` below.
        let unfold = match opts.artifact {
            Some(artifact) => format!("  unfold Quadcert.Gen.{artifact}.allTerms_{l}\n"),
            None => String::new(),
        };
        let terms = &layer_terms_expr[l];
        let mut body = String::new();
        for (j, (lo, len, bn)) in blocks.iter().enumerate() {
            body.push_str(&format!(
                "/-- Block {j}: groups [{lo}, {hi}), {bn} terms. -/\n\
                 theorem pblk_{l}_{j} :\n    \
                 (({terms}).filter (inBlk RawTerm.g {lo} {len})).Perm\n      \
                 ((List.range' {lo} {len}).flatMap groupOf_{l}) := by\n\
                 {unfold}  \
                 try simp only [List.filter_append]\n  \
                 exact perm_of_msort_eq rawLe {fuel} _ _ (by decide +kernel)\n\n",
                hi = lo + len
            ));
        }
        let bs = format!(
            "[{}]",
            blocks
                .iter()
                .map(|(lo, len, _)| format!("({lo}, {len})"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let m = format!("{name}Perm{l}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
                 import quadcert.Gen.{name}.{name}GroupDef{l}\nimport quadcert.Core.PermBlocks\n{term_imports}\
                 set_option maxRecDepth 10000000\nset_option maxHeartbeats 4000000\n\
                 namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
                 /-- Every term of layer {l} sits in a group below {gbound}. `perm_of_blocks`\n\
                 needs this: a term out of range would belong to no block, and the permutation\n\
                 would be false. -/\n\
                 theorem gbnd_{l} : ({terms}).all (fun t => decide (t.g < {gbound})) = true := by\n\
                 {unfold}  \
                 try simp only [List.all_append]\n  \
                 decide +kernel\n\n\
                 {body}\
                 /-- Layer {l}: {n} terms in {gbound} groups, {nblocks} blocks, `msort` fuel\n\
                 {fuel} per block. -/\n\
                 theorem perm_{l} :\n    \
                 ({terms}).Perm ((List.range {gbound}).flatMap groupOf_{l}) := by\n  \
                 refine perm_of_blocks RawTerm.g groupOf_{l} ({terms}) {gbound} {bs}\n    \
                 (by decide) ?_ ?_\n  \
                 · intro t ht\n    \
                 have h := List.all_eq_true.mp gbnd_{l} t ht\n    \
                 simpa using h\n  \
                 · intro b hb\n    \
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hb\n    \
                 rcases hb with {pats}\n\
                 {arms}\n\
                 end Quadcert.Gen.{name}\n",
                term_imports = term_mods
                    .iter()
                    .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                    .collect::<String>(),
                nblocks = blocks.len(),
                pats = vec!["rfl"; blocks.len()].join(" | "),
                arms = (0..blocks.len())
                    .map(|j| format!("    · exact pblk_{l}_{j}\n"))
                    .collect::<String>(),
            ),
        ));
        perm_mods.push(m);
        perm_arms.push_str(&format!("  · exact perm_{l}\n"));
    }

    let gbound_def = {
        fn btree(v: &[usize], lo: usize, hi: usize, base: usize) -> String {
            if hi - lo == 1 {
                return format!("{}", v[lo - base]);
            }
            let mid = lo + (hi - lo) / 2;
            format!(
                "(if L < {mid} then {} else {})",
                btree(v, lo, mid, base),
                btree(v, mid, hi, base)
            )
        }
        fn ftree(n: usize, lo: usize, hi: usize) -> String {
            if hi - lo == 1 {
                return format!("groupOf_{lo}");
            }
            let mid = lo + (hi - lo) / 2;
            format!(
                "(if L < {mid} then {} else {})",
                ftree(n, lo, mid),
                ftree(n, mid, hi)
            )
        }
        if nlayers == 0 {
            "def gbound : Nat → Nat := fun _ => 0\n\n\
             def groupOf : Nat → Nat → List RawTerm := fun _ _ => []\n\n"
                .to_string()
        } else {
            format!(
                "/-- Number of output wires per layer; `groupOkWith` checks `g` against it. -/\n\
                 def gbound : Nat → Nat := fun L =>\n  \
                 if L < {nlayers} then {} else 0\n\n\
                 def groupOf : Nat → Nat → List RawTerm := fun L =>\n  \
                 if L < {nlayers} then ({}) else fun _ => []\n\n",
                btree(&gbounds, 0, nlayers, 0),
                ftree(nlayers, 0, nlayers)
            )
        }
    };

    out.push((
        format!("Gen/{name}/{name}Groups.lean"),
        format!(
            "{}{gbound_def}\
             /-- Case analysis by *substitution*, not by `match`: matching on `L` gives the\n\
             equation compiler a motive mentioning `groupOf L`, and the resulting matcher type\n\
             carries the entire group tree — 5.7 GB before the kernel gave up. Rewriting `L` to a\n\
             literal first leaves `groupOf 3` reducible and the motive small. -/\n\
             theorem hom_all : ∀ L, L < {nlayers} → ∀ i, ∀ t ∈ groupOf L i, t.g = i := by\n  \
             intro L hL i t ht\n  \
             have hcase : {disj} := by omega\n  \
             rcases hcase with {pats}\n\
             {hom_arms}\n\
             end Quadcert.Gen.{name}\n",
            hdr(&group_def_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .chain(std::iter::once("import quadcert.Core.RawGroup\n".to_string()))
                .collect::<String>()),
        ),
    ));

    // The constant index that denotes zero. Materialized mid-circuit assertion terms carry it,
    // and `Backed` is stated in terms of it. If the table has no zero entry, any out-of-range
    // index works, because `constNat`'s catch-all is `0` — but then no assertion term can match
    // and `backed_check` fails, which is the correct outcome.
    let zero_const = s
        .constants
        .iter()
        .position(|c| c.iter().all(|b| *b == 0))
        .unwrap_or(s.constants.len());

    let assert_items: Vec<String> = s
        .assertions
        .iter()
        .map(|a| format!("⟨{}, {}, {}⟩", a.asserted_node, a.wire_layer, a.wire_index))
        .collect();

    // Per layer, the terms that are materialized mid-circuit assertions: coefficient zero.
    // `backed_check` matches each record against *these* rather than against the layer's whole
    // term list, which is the difference between `Σ_records (layer size)` and
    // `Σ_records (assertion terms on that layer)` — on ECDSA2, 4.2M term-steps against ~200k,
    // and the gap widens with circuit size because assertion count grows far more slowly than
    // term count. One `filter` equation per layer (11 scans, not 1,048) supplies the sublist
    // property `Check.azt_sub_of_filter` needs.
    let assert_terms: Vec<Vec<(u32, u32, u32, u32)>> = s
        .layers
        .iter()
        .map(|l| {
            l.terms
                .iter()
                .copied()
                .filter(|t| t.3 as usize == zero_const)
                .collect()
        })
        .collect();

    // Chunked **by cost, not by count**: measured, the kernel spends about 10 KB per term
    // scanned, and a fixed count of 64 put 24 records from the largest layers in one chunk and
    // blew a 3.5 GB cap while same-sized chunks on small layers finished in 26 s.
    const ASSERT_SCAN_BUDGET: usize = 150_000;
    let assert_cost = |a: &ParsedAssertion| -> usize {
        assert_terms.get(a.wire_layer).map_or(0, Vec::len)
    };
    let mut assert_chunks: Vec<Vec<String>> = Vec::new();
    {
        let mut cur: Vec<String> = Vec::new();
        let mut cost = 0usize;
        for (item, a) in assert_items.iter().zip(s.assertions.iter()) {
            let c = assert_cost(a);
            if !cur.is_empty() && cost + c > ASSERT_SCAN_BUDGET {
                assert_chunks.push(std::mem::take(&mut cur));
                cost = 0;
            }
            cur.push(item.clone());
            cost += c;
        }
        if !cur.is_empty() {
            assert_chunks.push(cur);
        }
    }
    let mut assert_mods = Vec::new();
    let mut assert_names = Vec::new();
    let mut backed_names = Vec::new();
    for (k, part) in assert_chunks.iter().enumerate() {
        let m = format!("{name}Asserts{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "{}def asserts_{k} : List RawAssert :=\n  [{}]\n\nend Quadcert.Gen.{name}\n",
                hdr(""),
                part.join(", ")
            ),
        ));
        assert_mods.push(m);
        assert_names.push(format!("asserts_{k}"));
        backed_names.push(format!("backed_{k}"));
    }
    let asserts_expr = if assert_names.is_empty() {
        "[]".to_string()
    } else {
        assert_names.join(" ++ ")
    };

    let mut doc = String::new();
    doc.push_str("--\n-- Constant table (advice; the spec module states the correspondence):\n");
    for (i, c) in s.constants.iter().enumerate() {
        let hex: String = c.iter().rev().map(|b| format!("{b:02x}")).collect();
        doc.push_str(&format!("--   c{i} = 0x{hex}\n"));
    }
    doc.push_str("--\n-- Input layout:\n");
    for (p, n) in &s.input_layout {
        doc.push_str(&format!("--   {p} = {n}\n"));
    }
    doc.push_str("--\n-- Assertion paths:\n");
    for a in &s.assertions {
        doc.push_str(&format!(
            "--   node {} @ ({},{})  {:?}\n",
            a.asserted_node, a.wire_layer, a.wire_index, a.paths
        ));
    }

    let layout_defs: String = s
        .input_layout
        .iter()
        .map(|(p, n)| format!("abbrev {n} : Nat := {p}\n"))
        .collect();

    let layout_pairs = s
        .input_layout
        .iter()
        .map(|(p, n)| format!("({p}, \"{n}\")"))
        .collect::<Vec<_>>()
        .join(", ");

    // With an artifact the sidecar is advice for exactly four fields, and everything else is
    // recovered from the committed bytes.  `artifactRaw_eq_raw` is the check that the two
    // halves describe one circuit.
    let (artifact_import, artifact_block) = match opts.artifact {
        None => (String::new(), String::new()),
        Some(artifact) => {
            // Same numbering as `FieldID` and `Quadcert.Lfc3`'s `FieldEncoding`s.
            let field = match s.field_id {
                1 => "p256",
                4 => "gf2_128",
                other => panic!("no Lean FieldEncoding for field id {other}"),
            };
            (
            format!("import quadcert.Gen.{artifact}.{artifact}Decode\n"),
            format!(
                "/-! ### Artifact refinement -/\n\n\
                 /-- The sidecar supplies structural advice, but no artifact dimensions, \
                 constants or terms. -/\n\
                 noncomputable def advice : Lfc3.RawAdvice where\n  \
                 nodes := {nodes}\n  wireFn := wireFn\n  asserts := {asserts}\n  \
                 layout := [{layout}]\n\n\
                 /-- The same circuit assembled with every artifact-owned field decoded from \
                 the committed LFC3 bytes. -/\n\
                 noncomputable def artifactRaw : RawCircuit :=\n  \
                 Quadcert.Gen.{artifact}.decoded.toRaw advice\n\n\
                 /-- Kernel-checked. The layer terms are *shared* with the artifact rather \
                 than copied, so what this checks is everything the sidecar claims \
                 independently: the dimensions, `logv`, `subfieldBoundary`, the constant \
                 count, and every layer's `nw`. -/\n\
                 theorem artifactRaw_eq_raw : artifactRaw = raw := by rfl\n\n\
                 /-- **Cite this, not `artifactRaw_eq_raw` alone.**  It is the step that makes \
                 a theorem about `raw` a theorem about the committed bytes: whatever those \
                 bytes decode to, extended by the sidecar's four advice fields, *is* `raw`.  \
                 Without it a spec theorem mentioning only `raw` says nothing about the \
                 artifact, because `raw` is a generated literal. -/\n\
                 theorem raw_from_bytes (c : Lfc3.DecodedCircuit)\n    \
                 (h : Lfc3.decode Lfc3.{field} Quadcert.Gen.{artifact}.packedInput\n      \
                 Quadcert.Gen.{artifact}.deltaTrees = .ok c) :\n    \
                 c.toRaw advice = raw := by\n  \
                 rw [Quadcert.Gen.{artifact}.decode_ok] at h\n  \
                 cases h\n  \
                 exact artifactRaw_eq_raw\n\n",
                nodes = node_names.join(" ++ "),
                asserts = asserts_expr,
                layout = layout_pairs,
            ),
            )
        }
    };

    let imports: String = std::iter::once(format!("import quadcert.Gen.{name}.{name}Base\n"))
        .chain(std::iter::once(artifact_import))
        .chain(term_mods.iter().map(|m| format!("import quadcert.Gen.{name}.{m}\n")))
        .chain(node_mods.iter().map(|m| format!("import quadcert.Gen.{name}.{m}\n")))
        .chain(assert_mods.iter().map(|m| format!("import quadcert.Gen.{name}.{m}\n")))
        .chain(inv_mods.iter().map(|m| format!("import quadcert.Gen.{name}.{m}\n")))
        .collect();

    let data = format!(
        "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n{doc}{imports}\
         set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
         namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
         /-! Input layout, from `LayoutBuilder`. -/\nnamespace Layout\n{layout_defs}end Layout\n\n\
         noncomputable def raw : RawCircuit where\n  \
         ninput := {ninput}\n  npublicInput := {npub}\n  noutput := {noutput}\n  \
         logv := {logv}\n  subfieldBoundary := {sfb}\n  \
         nconstants := {nconst}\n  layers := [{layers}]\n  nodes := {nodes}\n  \
         wireFn := wireFn\n  asserts := {asserts}\n  layout := [{layout}]\n\n\
         theorem nodes_len : raw.nodes.length = {nnodes} := by\n  \
         show ({nodes}).length = {nnodes}\n  \
         simp only [List.length_append, {lens}]\n\n\
         /-- The dumper guards `wireFn`, so range-confinement is three lines. -/\n\
         theorem wireFn_lt : ∀ i p, raw.wireFn i = some p → i < raw.nodes.length := by\n  \
         intro i p h\n  rw [nodes_len]\n  by_cases hc : i < {nnodes}\n  \
         · exact hc\n  \
         · exfalso\n    \
         have hnone : raw.wireFn i = none := by\n      \
         show wireFn i = none\n      \
         simp only [wireFn, if_neg hc]\n    \
         rw [hnone] at h\n    exact absurd h (by simp)\n\n\
         {artifact_block}\
         end Quadcert.Gen.{name}\n",
        ninput = s.ninput,
        npub = s.npublic_input,
        noutput = s.noutput,
        logv = s.logv,
        sfb = s.subfield_boundary,
        nconst = s.constants.len(),
        layers = layer_defs.join(", "),
        nodes = node_names.join(" ++ "),
        asserts = asserts_expr,
        layout = layout_pairs,
        lens = len_names.join(", "),
    );
    out.push((format!("Gen/{name}/{name}Data.lean"), data));

    // The two checks live in their own modules: each is a large single term, and keeping
    // them apart both bounds per-module cost and makes `lake` report their cost separately.
    out.push((
        format!("Gen/{name}/{name}OkCheck.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Data\n\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- Composed from the per-chunk slices; no whole-circuit `decide`. -/\n\
             theorem ok_check : raw.ok = true := by\n  \
             show ((raw.nodes).zipIdx 0).all (fun p => raw.okNodeAt p.1 p.2) = true\n  \
             simp only [okNodeAt_eq]\n  \
             show (({nodes}).zipIdx 0).all (fun p => okNodeWith wireFn nlayers p.1 p.2) = true\n  \
             simp only [List.zipIdx_append, List.all_append, List.length_append, {lens},\n    \
             Nat.zero_add, Nat.reduceAdd, {oks}, Bool.and_self]\n\n\
             end Quadcert.Gen.{name}\n",
            name = name,
            nodes = node_names.join(" ++ "),
            lens = len_names.join(", "),
            oks = ok_names.join(", "),
        ),
    ));
    // ---- node bisection -------------------------------------------------------
    //
    // `raw.nodes` is an append of chunk literals, so `nodes.getD n` allocates a cons per element
    // traversed and re-does it every lookup. A per-assertion meaning lemma needs one `getD` per
    // node of its cone -- 118 for an ECDSA2 `slice_wx` -- and measured, that timed out at the
    // 65th. This is the same bisection `wireFn` uses, checked against the list *sequentially*:
    // one pass over `nodes.zipIdx`, not one lookup per node.
    fn ntree(items: &[String], lo: usize, hi: usize, base: usize) -> String {
        if hi - lo == 1 {
            return items[lo - base].clone();
        }
        let mid = lo + (hi - lo) / 2;
        format!(
            "(if i < {mid} then {} else {})",
            ntree(items, lo, mid, base),
            ntree(items, mid, hi, base)
        )
    }
    let mut nodefn_mods = Vec::new();
    let mut nodefn_chk_mods: Vec<String> = Vec::new();
    let mut nodefn_dispatch = String::new();
    let mut nodefn_chk_names = Vec::new();
    for (k, part) in node_items.chunks(nstep).enumerate() {
        let lo = k * nstep;
        let hi = lo + part.len();
        let m = format!("{name}NodeFn{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "{}def nodeFn_{k} : Nat → RawNode := fun i =>\n  {}\n\n\
                 end Quadcert.Gen.{name}\n",
                hdr(""),
                ntree(part, lo, hi, lo)
            ),
        ));
        nodefn_mods.push(m);
        nodefn_dispatch.push_str(&format!("if i < {hi} then nodeFn_{k} i else "));
        nodefn_chk_names.push(format!("nodefn_{k}"));
    }
    nodefn_dispatch.push_str(".input 0");
    let nodefn_dispatch = format!("if i < {nnodes} then ({nodefn_dispatch}) else .input 0");
    out.push((
        format!("Gen/{name}/{name}NodeFn.lean"),
        format!(
            "{}noncomputable def nodeFn : Nat → RawNode := fun i =>\n  {nodefn_dispatch}\n\n\
             end Quadcert.Gen.{name}\n",
            hdr(&nodefn_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .collect::<String>())
        ),
    ));
    for (k, part) in node_items.chunks(nstep).enumerate() {
        let off = k * nstep;
        let _ = part;
        let m = format!("{name}NodeChk{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
                 import quadcert.Gen.{name}.{name}Nodes{k}\nimport quadcert.Gen.{name}.{name}NodeFn\n\
                 import quadcert.Core.RawGroup\n\
                 set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
                 namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
                 /-- This chunk's slice of the bisection check. -/\n\
                 theorem nodefn_{k} :\n    \
                 ((nodes_{k}).zipIdx {off}).all (fun p => nodeEq (nodeFn p.2) p.1) = true := by\n    \
                 decide +kernel\n\n\
                 end Quadcert.Gen.{name}\n"
            ),
        ));
        nodefn_chk_mods.push(m);
    }

    // Per-node correspondence, one module per node chunk, exactly the shape `ok_k` uses. Each
    // is local: a node's obligation mentions its own group, not its layer.
    // **`decide +kernel`, not `decide`.** Every bulk check in this emitter goes to the kernel
    // evaluator rather than the elaborator's `whnf`. Measured on SHA-256's layer chunks, where
    // the two differ by orders of magnitude and not uniformly:
    //
    //   corr_15        20,366 s / 10.4 GB  ->  51 s / 10.0 GB      (400x)
    //   commitment_19     827 s /  2.8 GB  ->  11 s /  2.7 GB       (75x)
    //   ok_17             136 s / 12.1 GB  ->  85 s / 11.7 GB      (1.6x)
    //
    // The spread is the tell: elaborator `decide` degrades on the chunks holding the wide `sum`
    // nodes, so a chunking that looks uniform by node count is wildly non-uniform by cost. It
    // cost 5.7 hours in one module before anyone looked. Time moves; peak memory barely does,
    // so the `-M` cap is a separate knob and is set from these numbers.
    let mut corr_mods = Vec::new();
    let mut corr_names = Vec::new();
    for (k, part) in node_items.chunks(nstep).enumerate() {
        let off = k * nstep;
        let _ = part;
        let m = format!("{name}Corr{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
                 import quadcert.Gen.{name}.{name}Nodes{k}\nimport quadcert.Gen.{name}.{name}Groups\n\
                 import quadcert.Core.RawGroup\n\
                 set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
                 namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
                 /-- This chunk's slice of the `sum_local` correspondence. -/\n\
                 theorem corr_{k} :\n    \
                 ((nodes_{k}).zipIdx {off}).all\n      \
                 (fun p => groupOkWith wireFn gbound groupOf p.1 p.2) = true := by decide +kernel\n\n\
                 end Quadcert.Gen.{name}\n"
            ),
        ));
        corr_mods.push(m);
        corr_names.push(format!("corr_{k}"));
    }

    out.push((
        format!("Gen/{name}/{name}NodeChk.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Data\nimport quadcert.Gen.{name}.{name}NodeFn\n\
             import quadcert.Core.RawGroup\n{imports}\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- The bisection agrees with the node list everywhere. One sequential pass,\n\
             composed from the per-chunk slices; `Check.toDag_getD_fn` turns it into O(log n)\n\
             node lookups for the meaning lemmas. -/\n\
             theorem nodefn_ok :\n    \
             (raw.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true := by\n  \
             show (({nodes}).zipIdx 0).all (fun p => nodeEq (nodeFn p.2) p.1) = true\n  \
             simp only [List.zipIdx_append, List.all_append, List.length_append, {lens},\n    \
             Nat.zero_add, Nat.reduceAdd, {chks}, Bool.and_self]\n\n\
             end Quadcert.Gen.{name}\n",
            imports = nodefn_chk_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .collect::<String>(),
            nodes = node_names.join(" ++ "),
            lens = len_names.join(", "),
            chks = nodefn_chk_names.join(", "),
        ),
    ));
    out.push((
        format!("Gen/{name}/{name}SumLocal.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Data\nimport quadcert.Core.RawGroup\n{perm_imports}{corr_imports}\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- The layer permutations, assembled. `raw.layers.length` reduces to {nlayers}. -/\n\
             theorem perm_all : ∀ L, L < {nlayers} →\n    \
             (raw.layers.getD L ⟨0, []⟩).terms.Perm\n      \
             ((List.range (gbound L)).flatMap (groupOf L)) := by\n  \
             intro L hL\n  \
             have hcase : {disj} := by omega\n  \
             rcases hcase with {pats}\n\
             {perm_arms}\n\
             /-- Composed from the per-chunk slices; no whole-circuit `decide`. -/\n\
             theorem corr_check :\n    \
             raw.nodes.zipIdx.all\n      \
             (fun p => groupOkWith raw.wireFn gbound groupOf p.1 p.2) = true := by\n  \
             show (({nodes}).zipIdx 0).all\n      \
             (fun p => groupOkWith wireFn gbound groupOf p.1 p.2) = true\n  \
             simp only [List.zipIdx_append, List.all_append, List.length_append, {lens},\n    \
             Nat.zero_add, Nat.reduceAdd, {corrs}, Bool.and_self]\n\n\
             end Quadcert.Gen.{name}\n",
            perm_imports = perm_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .collect::<String>(),
            corr_imports = corr_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .collect::<String>(),
            nodes = node_names.join(" ++ "),
            lens = len_names.join(", "),
            corrs = corr_names.join(", "),
        ),
    ));



    // `zeroConst` and the per-layer assertion terms, in one small module every `backed_k` and
    // `filt_L` can name.
    let azt_defs: String = assert_terms
        .iter()
        .enumerate()
        .map(|(l, ts)| {
            format!(
                "def assertTerms_{l} : List RawTerm :=\n  [{}]\n\n",
                ts.iter()
                    .map(|(g, h0, h1, k)| format!("⟨{g}, {h0}, {h1}, {k}⟩"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect();
    fn azt_tree(n: usize, lo: usize, hi: usize) -> String {
        if hi - lo == 1 {
            return format!("assertTerms_{lo}");
        }
        let mid = lo + (hi - lo) / 2;
        format!(
            "(if L < {mid} then {} else {})",
            azt_tree(n, lo, mid),
            azt_tree(n, mid, hi)
        )
    }
    let azt_def = if nlayers == 0 {
        "def azt : Nat → List RawTerm := fun _ => []\n".to_string()
    } else {
        format!(
            "/-- The assertion terms of each layer; `[]` outside the circuit. -/\n\
             def azt : Nat → List RawTerm := fun L =>\n  \
             if L < {nlayers} then {} else []\n",
            azt_tree(nlayers, 0, nlayers)
        )
    };
    out.push((
        format!("Gen/{name}/{name}Zero.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Data\nimport quadcert.Core.RawGroup\n\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- The constant index denoting zero, in the **artifact's** numbering: the sidecar\n\
             is built from the segmented circuit, so the two tables agree. -/\n\
             abbrev zeroConst : Nat := {zero_const}\n\n\
             {azt_defs}{azt_def}\n\
             end Quadcert.Gen.{name}\n"
        ),
    ));

    // One `filter` scan per layer. This is the whole cost of relating `azt` to the artifact.
    //
    // **Scanned chunk by chunk, and that is not optional.**  A bare `decide +kernel` over a
    // whole layer holds every intermediate `List.filter` cell of the literal at once: SHA-256's
    // 89,048-term layer 5 peaked at 32.1 GB, over this machine's entire budget, while the
    // 26,000-term layer 4 took 3.9 GB — the cost grows far faster than the term count.
    // Distributing the filter over the emitted chunks first drops layer 5 to **1.7 GB and 7 s**,
    // because each chunk's filter then reduces and is released independently.
    //
    // `List.filter_append` is used rather than named per-chunk lemmas precisely so this needs no
    // chunk metadata: whatever decomposition the term module happens to carry — the artifact's
    // expansion chunks, this emitter's `layerTerms{l}_{j}`, or a single flat literal — `unfold`
    // exposes it and the rewrite splits along it.  Hence the `try`: a one-chunk layer has no
    // `++` for `simp` to make progress on.
    let mut filt_mods = Vec::new();
    let mut filt_names = Vec::new();
    for l in 0..nlayers {
        let m = format!("{name}Filt{l}");
        let terms_expr = &layer_terms_expr[l];
        // With an artifact the layer is a single opaque name and its chunking lives behind the
        // definition; without one, `layer_terms_expr` already spells the chunks out.
        let unfold = match opts.artifact {
            Some(artifact) => format!("  unfold Quadcert.Gen.{artifact}.allTerms_{l}\n"),
            None => String::new(),
        };
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
                 import quadcert.Gen.{name}.{name}Zero\n\
                 set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
                 namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
                 /-- Layer {l}'s assertion terms are exactly its zero-coefficient terms. One scan\n\
                 of the layer, chunk by chunk; every record on it then matches against the short\n\
                 list. -/\n\
                 theorem filt_{l} :\n    \
                 (raw.layers.getD {l} ⟨0, []⟩).terms.filter (fun t => t.kIndex == zeroConst)\n      \
                 = azt {l} := by\n  \
                 show ({terms_expr}).filter (fun t => t.kIndex == zeroConst) = azt {l}\n\
                 {unfold}  \
                 try simp only [List.filter_append]\n  \
                 decide +kernel\n\n\
                 end Quadcert.Gen.{name}\n"
            ),
        ));
        filt_mods.push(m);
        filt_names.push(format!("filt_{l}"));
    }
    let mut backed_mods = Vec::new();
    for k in 0..assert_chunks.len() {
        let m = format!("{name}Backed{k}");
        out.push((
            format!("Gen/{name}/{m}.lean"),
            format!(
                "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
                 import quadcert.Gen.{name}.{name}Zero\n\
                 set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
                 namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
                 /-- This chunk's slice of the soundness half of the assertion bridge. -/\n\
                 theorem backed_{k} :\n    \
                 (asserts_{k}).all (backedRawWith raw zeroConst azt) = true := by\n    \
                 decide +kernel\n\n\
                 end Quadcert.Gen.{name}\n"
            ),
        ));
        backed_mods.push(m);
    }
    out.push((
        format!("Gen/{name}/{name}Backed.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Zero\n{imports}\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- Every assertion record is carried by a real circuit constraint. This is the\n\
             half of the assertion bridge that ZK **soundness** consumes; the converse\n\
             (`CoversConstraints`, no unnamed constraint) is a separate check.\n\n\
             Composed from the per-chunk slices: one `decide` over all {nasserts} records scans\n\
             each against its layer's whole term list and exceeds a 3.5 GB kernel cap. -/\n\
             theorem backed_check :\n    \
             raw.asserts.all (backedRawWith raw zeroConst azt) = true := by\n  \
             show ({asserts}).all (backedRawWith raw zeroConst azt) = true\n  \
             simp only [List.all_append, {backeds}, Bool.and_self]\n\n\
             /-- Every `azt` entry really is a term of its layer. Assembled from the per-layer\n\
             `filter` equations; out of range both sides are `[]`. -/\n\
             theorem azt_sub : ∀ L, ∀ t ∈ azt L, t ∈ (raw.layers.getD L ⟨0, []⟩).terms := by\n  \
             intro L t ht\n  \
             by_cases hL : L < {nlayers}\n  \
             · have hcase : {disj} := by omega\n    \
             rcases hcase with {pats}\n\
             {arms}  \
             · have hz : azt L = [] := by unfold azt; rw [if_neg hL]\n    \
             rw [hz] at ht\n    \
             exact absurd ht (by simp)\n\n\
             end Quadcert.Gen.{name}\n",
            arms = (0..nlayers)
                .map(|l| format!(
                    "    · exact azt_sub_of_filter raw zeroConst azt {l} filt_{l} t ht\n"
                ))
                .collect::<String>(),
            imports = backed_mods
                .iter()
                .map(|m| format!("import quadcert.Gen.{name}.{m}\n"))
                .chain(filt_mods.iter().map(|m| format!("import quadcert.Gen.{name}.{m}\n")))
                .collect::<String>(),
            nasserts = assert_items.len(),
            asserts = asserts_expr,
            backeds = backed_names.join(", "),
        ),
    ));

    // ---- template schemas ----------------------------------------------------
    //
    // One Lean theorem per template shape, with the template's nodes as parameters. The
    // expensive part of a meaning lemma — unfolding `interpDag` and normalising — happens
    // once per *shape*; each instance then supplies its own nodes and discharges the
    // structural hypotheses by `rfl`. Instances cannot be indexed arithmetically (their node
    // indices and input positions are irregular), which is exactly why the parameters are
    // nodes rather than a loop index.
    fn tmpl_expr(t: &Template, i: usize, budget: &mut usize) -> Option<String> {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        match &t.nodes[i] {
            TemplateNode::Leaf(_) => Some(format!("interpDag dag inputs m{i}")),
            TemplateNode::Sum(ts) => {
                let mut acc = "0".to_string();
                for (k, a, b) in ts {
                    let ea = tmpl_expr(t, *a as usize, budget)?;
                    let eb = tmpl_expr(t, *b as usize, budget)?;
                    acc = format!("({acc} + consts {k} * ({ea}) * ({eb}))");
                }
                Some(acc)
            }
        }
    }
    let mut schemas = String::new();
    for (ti, t) in s.templates.iter().enumerate() {
        let root = t.nodes.len() - 1;
        let mut budget = 400usize;
        let Some(rhs) = tmpl_expr(t, root, &mut budget) else {
            schemas.push_str(&format!(
                "-- template {ti} omitted: expansion exceeds the inlining budget\n"
            ));
            continue;
        };
        let params: String = (0..t.nodes.len())
            .map(|i| format!("m{i} "))
            .collect::<String>();
        let mut hyps = String::new();
        let mut rws = Vec::new();
        for (i, nd) in t.nodes.iter().enumerate() {
            if let TemplateNode::Sum(ts) = nd {
                let terms: Vec<String> = ts
                    .iter()
                    .map(|(k, a, b)| format!("⟨consts {k}, m{a}, m{b}⟩"))
                    .collect();
                hyps.push_str(&format!(
                    "    (h{i} : dag.getD m{i} (.input 0) = .sum [{}])\n",
                    terms.join(", ")
                ));
                rws.push(format!(
                    "interpDag_sum inputs dag m{i} _ h{i} (vs.sum_operands_lt m{i} _ h{i})"
                ));
            }
        }
        schemas.push_str(&format!(
            "/-- Schema for template {ti} ({} nodes, {} leaves). -/\n\
             theorem tmpl{ti} {{c : QuadCircuitData F}} {{dag : List (DagNode F)}}\n    \
             {{wireMap : WireMap}} {{inputs : Nat → F}}\n    \
             (vs : ValidScheduling c dag wireMap inputs) (consts : Nat → F)\n    \
             ({params}: Nat)\n{hyps}    : interpDag dag inputs m{root} = {rhs} := by\n  \
             simp only [{}List.foldl_cons, List.foldl_nil]\n  try ring\n\n",
            t.nodes.len(),
            t.nleaves,
            // `simp only` rather than ordered `rw`: it runs to fixpoint, so the unfolding
            // and the fold-elimination interleave without the caller choosing an order.
            // A template whose root is a bare leaf has no unfolding to do, and the trailing
            // separator must not be emitted then -- `simp only [, ...]` is a parse error.
            if rws.is_empty() {
                String::new()
            } else {
                format!("{},\n    ", rws.join(",\n    "))
            }
        ));
    }
    out.push((
        format!("Gen/{name}/{name}Schemas.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Core.Semantics\n\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 1000000\n\
             namespace Quadcert.Gen.{name}.Schemas\n\
             variable {{F : Type}} [Field F]\n\n{schemas}\n\
             end Quadcert.Gen.{name}.Schemas\n"
        ),
    ));

    out.push((
        format!("Gen/{name}/{name}InvCheck.lean"),
        format!(
            "-- Generated by `compile_compiler::cert::emit_lean`. Do not edit.\n\
             import quadcert.Gen.{name}.{name}Data\n\
             set_option maxRecDepth 4000000\nset_option maxHeartbeats 4000000\n\
             namespace Quadcert.Gen.{name}\nopen Quadcert\n\n\
             /-- Composed from the per-chunk slices via a contiguous tiling; no\n\
             whole-circuit `decide`. -/\n\
             theorem inv_check : raw.okInv wireInv = true := by\n  \
             refine okInv_of_chunks raw wireInv [{ranges}] ?_ ?_\n  \
             · rw [nodes_len]; decide\n  \
             · show okInvChunks wireFn wireInv [{ranges}] = true\n    \
             simp only [okInvChunks, List.all_cons, List.all_nil, {invs}, Bool.and_self,\n      \
             Bool.and_true]\n\n\
             end Quadcert.Gen.{name}\n",
            name = name,
            ranges = ranges.join(", "),
            invs = inv_names.join(", "),
        ),
    ));
    let _ = &lensum;
    out
}
