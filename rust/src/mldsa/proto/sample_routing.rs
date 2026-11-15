// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public switch order and pruning for the fixed256-record Beneš networks.
pub(crate) const ROUTING_SIZE: usize = 256;
pub(crate) struct RoutingPlan {
    pub pairs: Vec<(usize, usize)>,
    pub active: Vec<bool>,
}
/// Keep only switches affecting the requested output prefix, and omit switches
/// whose two inputs are publicly known zero padding. Omitted switches are fixed
/// to false; the resulting network remains an exact permutation of all records.
pub(crate) fn routing_plan(outputs: usize, inputs: usize) -> RoutingPlan {
    assert!(outputs <= ROUTING_SIZE && inputs <= ROUTING_SIZE);
    fn append(indices: &[usize], pairs: &mut Vec<(usize, usize)>) {
        if indices.len() < 2 {
            return;
        }
        pairs.extend(indices.as_chunks::<2>().0.iter().map(|p| (p[0], p[1])));
        if indices.len() > 2 {
            let even: Vec<_> = indices.iter().step_by(2).copied().collect();
            let odd: Vec<_> = indices.iter().skip(1).step_by(2).copied().collect();
            append(&even, pairs);
            append(&odd, pairs);
            pairs.extend(indices.as_chunks::<2>().0.iter().map(|p| (p[0], p[1])));
        }
    }
    let mut full = Vec::new();
    append(&(0..ROUTING_SIZE).collect::<Vec<_>>(), &mut full);
    let mut live = vec![false; ROUTING_SIZE];
    live[..outputs].fill(true);
    let mut active = vec![false; full.len()];
    for (i, &(a, b)) in full.iter().enumerate().rev() {
        if live[a] || live[b] {
            active[i] = true;
            live[a] = true;
            live[b] = true;
        }
    }
    let mut zero = vec![false; ROUTING_SIZE];
    zero[inputs..].fill(true);
    for (i, &(a, b)) in full.iter().enumerate() {
        if active[i] {
            if zero[a] && zero[b] {
                active[i] = false;
            } else {
                zero[a] = false;
                zero[b] = false;
            }
        }
    }
    let pairs = full
        .into_iter()
        .zip(&active)
        .filter_map(|(p, &keep)| keep.then_some(p))
        .collect();
    RoutingPlan { pairs, active }
}
