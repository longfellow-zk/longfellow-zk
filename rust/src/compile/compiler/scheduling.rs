// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared scheduling data, input validation and assertion-symbol extraction.

use crate::{
    compile::{algebra::field::CompileField, compiler::graph::Node, logic::scope::AssertionId},
    core::algebra::ElementOf,
};

#[derive(Debug, Clone, Copy)]
pub(super) struct WireId {
    pub(super) id_within_layer: usize,
}

pub(super) const INVALID_WIRE_ID: WireId = WireId {
    id_within_layer: usize::MAX,
};

pub(super) struct RenamedTerm<F: CompileField + crate::core::algebra::SerializableField> {
    pub(super) k: ElementOf<F>,
    pub(super) rlop0: usize,
    pub(super) rlop1: usize,
}

impl<F: CompileField + crate::core::algebra::SerializableField> RenamedTerm<F> {
    pub(super) fn compare(&self, other: &Self, f: &F) -> std::cmp::Ordering {
        self.rlop1
            .cmp(&other.rlop1)
            .then(self.rlop0.cmp(&other.rlop0))
            .then_with(|| f.to_bytes(&self.k).cmp(&f.to_bytes(&other.k)))
    }
}

pub(super) struct RenamedNode<F: CompileField + crate::core::algebra::SerializableField> {
    pub(super) original_node_index: usize,
    pub(super) rlterms: Vec<RenamedTerm<F>>,
}

impl<F: CompileField + crate::core::algebra::SerializableField> RenamedNode<F> {
    pub(super) fn compare(&self, other: &Self, f: &F) -> std::cmp::Ordering {
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

pub(super) fn validate_and_count_inputs<T>(nodes: &[Node<T>]) -> usize {
    let mut ninput_wires = 0;
    let mut max_input_pos = 0;
    for n in nodes {
        if let Node::Input {
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

pub(super) fn extract_debug_symbols<T>(
    nodes: &[Node<T>],
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
                Node::Assert0(w) => w,
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
