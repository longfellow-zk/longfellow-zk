// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Cone analysis for the meaning layer: copy canonicalisation, expansion cost, and the frontier
//! at which a cone stops being expandable.
//!
//! An assertion's meaning lemma is proved by expanding its DAG cone into a polynomial over some
//! set of atoms. Which atoms is the whole question. Expanding all the way to input wires works
//! only while the polynomial stays small; for the ECDSA2 loop rounds it is 2,284,051 monomials,
//! which `ring` cannot do. The cut that works holds a few expensive interior nodes opaque, and
//! finding it was previously a search over candidate boundaries (`formal/tools/gen_loop_meaning.py`).
//!
//! It does not need to be a search. Two observations make it deterministic:
//!
//! * **Copies are noise.** `copy::` lifts a value across a layer by multiplying it by the
//!   constant one, so the same value reappears under a fresh id at every layer it crosses.
//!   Measured on ECDSA2, 9,031 of 26,939 nodes are such copies. Canonicalising them removes ~37%
//!   of a loop cone and, more importantly, stops a shared value from looking unshared.
//!
//! * **Cost is computable.** Every node is a quadratic form, so the monomial count of a full
//!   expansion follows bottom-up: `cost(input) = 1`, `cost(sum) = Σ cost(a)·cost(b)`.
//!
//! The frontier then *grows* rather than being thresholded: start with only the root expanded and
//! repeatedly expand the cheapest remaining atom while the root total still fits a budget. A
//! global threshold does not work — `cost` is monotone up the DAG, so "expand iff cost ≤ θ"
//! expands a node entirely or not at all and cannot express an interior cut.
//!
//! Validated against the two cuts that were previously placed by hand, matching them by identity:
//!
//! * `ecdsa/e_eq` yields 257 atoms with only the root expanded — the 256 table evaluations plus
//!   the witness, which is what `gen_bitsum_meaning.py` cuts by hand.
//! * `slice_wy` at budget 512 yields exactly three interior atoms, nodes at wires (5,102),
//!   (5,103) and (5,104) costing 690, 1440 and 1440 — the three table outputs
//!   `gen_loop_meaning.py` holds opaque. They survive every budget because expanding a degree-7
//!   interpolant is where the monomial count explodes, so the budget behaves as a floor rather
//!   than a tuning knob.

use std::collections::{BTreeSet, HashMap};

use crate::cert::{ParsedNode, ParsedSidecar};

/// Per-node analysis of a sidecar's DAG: which nodes are the constant one, which are copies of
/// an earlier value, and what a full expansion would cost.
pub struct Cones {
    /// `true` for nodes that are identically 1.
    pub is_unit: Vec<bool>,
    /// Representative of each node after copy chains are collapsed; `canon[n] <= n`.
    pub canon: Vec<usize>,
    /// Monomial count of a full expansion to inputs, saturating.
    pub cost: Vec<u64>,
}

/// The chosen cut for one assertion.
pub struct Frontier {
    /// Canonical root the cut is about.
    pub root: usize,
    /// Nodes expanded into the polynomial.
    pub expanded: BTreeSet<usize>,
    /// Nodes held opaque; the polynomial's variables.
    pub atoms: BTreeSet<usize>,
    /// Monomial count at the root under this cut.
    pub total: u64,
}

/// Field constants are little-endian, so one is `[1, 0, 0, ...]`.
fn is_one(bytes: &[u8]) -> bool {
    bytes.first() == Some(&1) && bytes[1..].iter().all(|&b| b == 0)
}

impl Cones {
    /// Canonicalise copies and compute expansion cost. One forward pass suffices: operands
    /// precede their parent in `nodes`, so `canon` and `cost` are final when a parent reads them.
    pub fn new(s: &ParsedSidecar) -> Self {
        let one_pos = s
            .input_layout
            .iter()
            .find(|(_, name)| name == "one")
            .map(|(pos, _)| *pos);
        let n = s.nodes.len();
        let mut is_unit = vec![false; n];
        let mut canon: Vec<usize> = (0..n).collect();
        for i in 0..n {
            match &s.nodes[i] {
                ParsedNode::Input { position } => {
                    if Some(*position) == one_pos {
                        is_unit[i] = true;
                    }
                }
                ParsedNode::Sum { terms } => {
                    // A copy is `1 * a * b` with one operand the constant one.
                    if terms.len() == 1 {
                        let (k, a, b) = terms[0];
                        if is_one(&s.constants[k as usize]) {
                            if is_unit[a] && is_unit[b] {
                                is_unit[i] = true;
                            } else if is_unit[a] {
                                canon[i] = canon[b];
                            } else if is_unit[b] {
                                canon[i] = canon[a];
                            }
                        }
                    }
                }
                ParsedNode::Assert0 { .. } => {}
            }
        }
        let mut cost = vec![1u64; n];
        for i in 0..n {
            if let ParsedNode::Sum { terms } = &s.nodes[i] {
                let mut c: u64 = 0;
                for &(_, a, b) in terms {
                    let (ca, cb) = (canon[a], canon[b]);
                    let va = if is_unit[ca] { 1 } else { cost[ca] };
                    let vb = if is_unit[cb] { 1 } else { cost[cb] };
                    c = c.saturating_add(va.saturating_mul(vb));
                }
                cost[i] = c.max(1);
            }
        }
        Self {
            is_unit,
            canon,
            cost,
        }
    }

    /// Nodes of `root`'s cone in topological order, operands first, following canonical operands
    /// and skipping units.
    pub fn cone(&self, s: &ParsedSidecar, root: usize) -> Vec<usize> {
        let mut order = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![(root, false)];
        while let Some((n, emit)) = stack.pop() {
            if emit {
                order.push(n);
                continue;
            }
            if !seen.insert(n) {
                continue;
            }
            stack.push((n, true));
            if let ParsedNode::Sum { terms } = &s.nodes[n] {
                for &(_, x, y) in terms {
                    for op in [self.canon[x], self.canon[y]] {
                        if !self.is_unit[op] && !seen.contains(&op) {
                            stack.push((op, false));
                        }
                    }
                }
            }
        }
        order
    }

    /// Monomial count at `root` when exactly `expanded` is expanded and everything else is an
    /// atom worth one monomial.
    pub fn total(
        &self,
        s: &ParsedSidecar,
        order: &[usize],
        root: usize,
        expanded: &BTreeSet<usize>,
    ) -> u64 {
        let mut eff: HashMap<usize, u64> = HashMap::with_capacity(order.len());
        for &n in order {
            let v = match &s.nodes[n] {
                ParsedNode::Sum { terms } if expanded.contains(&n) => {
                    let mut t: u64 = 0;
                    for &(_, x, y) in terms {
                        let g = |o: usize| -> u64 {
                            if self.is_unit[o] {
                                1
                            } else {
                                *eff.get(&o).unwrap_or(&1)
                            }
                        };
                        t = t.saturating_add(
                            g(self.canon[x]).saturating_mul(g(self.canon[y])),
                        );
                    }
                    t.max(1)
                }
                _ => 1,
            };
            eff.insert(n, v);
        }
        *eff.get(&root).unwrap_or(&1)
    }

    /// Grow the expansion cheapest-first while the root total fits `budget`.
    ///
    /// Deterministic: candidates are ordered by `(cost, id)`, so the cut depends only on the
    /// circuit and the budget. The root is always expanded — a lemma has to say something about
    /// it — so a root whose every operand is expensive yields those operands as the atoms, which
    /// is the bit-sum case.
    pub fn frontier(&self, s: &ParsedSidecar, root: usize, budget: u64) -> Frontier {
        let root = self.canon[root];
        let order = self.cone(s, root);
        let mut expanded: BTreeSet<usize> = BTreeSet::new();
        expanded.insert(root);
        loop {
            let mut cands: Vec<usize> = Vec::new();
            for &n in expanded.iter() {
                if let ParsedNode::Sum { terms } = &s.nodes[n] {
                    for &(_, x, y) in terms {
                        for op in [self.canon[x], self.canon[y]] {
                            if self.is_unit[op] || expanded.contains(&op) {
                                continue;
                            }
                            if matches!(&s.nodes[op], ParsedNode::Sum { .. }) {
                                cands.push(op);
                            }
                        }
                    }
                }
            }
            cands.sort_by_key(|&n| (self.cost[n], n));
            cands.dedup();
            let Some(&pick) = cands.first() else { break };
            expanded.insert(pick);
            if self.total(s, &order, root, &expanded) > budget {
                expanded.remove(&pick);
                break;
            }
        }
        let mut atoms: BTreeSet<usize> = BTreeSet::new();
        for &n in expanded.iter() {
            if let ParsedNode::Sum { terms } = &s.nodes[n] {
                for &(_, x, y) in terms {
                    for op in [self.canon[x], self.canon[y]] {
                        if !self.is_unit[op] && !expanded.contains(&op) {
                            atoms.insert(op);
                        }
                    }
                }
            }
        }
        let total = self.total(s, &order, root, &expanded);
        Frontier {
            root,
            expanded,
            atoms,
            total,
        }
    }

    /// `(units, copies, nodes carrying content)`.
    pub fn stats(&self) -> (usize, usize, usize) {
        let units = self.is_unit.iter().filter(|u| **u).count();
        let copies = (0..self.canon.len()).filter(|&n| self.canon[n] != n).count();
        (units, copies, self.canon.len() - units - copies)
    }
}
