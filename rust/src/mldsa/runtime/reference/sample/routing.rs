// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Native route construction; the circuit checks every switch independently.
#[cfg(test)]
mod tests;
/// Selectors for a permutation mapping each input index to its output index.
pub(super) fn switches(permutation: &[usize]) -> Vec<bool> {
    let n = permutation.len();
    assert!(n.is_power_of_two());
    if n == 1 {
        return Vec::new();
    }
    if n == 2 {
        assert!(permutation == [0, 1] || permutation == [1, 0]);
        return vec![permutation[0] == 1];
    }
    let mut inverse = vec![usize::MAX; n];
    for (i, &j) in permutation.iter().enumerate() {
        assert!(j < n && inverse[j] == usize::MAX);
        inverse[j] = i;
    }
    // The input-pair and output-pair matchings form disjoint even cycles.
    // Opposite colors select opposite recursive subnetworks at both ends.
    let mut color = vec![None; n];
    for root in 0..n {
        if color[root].is_some() {
            continue;
        }
        color[root] = Some(false);
        let mut pending = vec![root];
        while let Some(i) = pending.pop() {
            let c = color[i].unwrap();
            for j in [i ^ 1, inverse[permutation[i] ^ 1]] {
                if let Some(other) = color[j] {
                    assert_eq!(other, !c);
                } else {
                    color[j] = Some(!c);
                    pending.push(j);
                }
            }
        }
    }
    let mut result: Vec<_> = (0..n).step_by(2).map(|i| color[i].unwrap()).collect();
    for branch in [false, true] {
        let mut sub = vec![usize::MAX; n / 2];
        for i in 0..n {
            if color[i] == Some(branch) {
                sub[i / 2] = permutation[i] / 2;
            }
        }
        result.extend(switches(&sub));
    }
    result.extend((0..n).step_by(2).map(|j| color[inverse[j]].unwrap()));
    result
}

/// Controls of the public pruned network in the shared circuit contract.
pub(super) fn partial_switches(permutation: &[usize], outputs: usize, inputs: usize) -> Vec<bool> {
    use crate::mldsa::proto::{routing_plan, RoutingPlan};
    let plan: RoutingPlan = routing_plan(outputs, inputs);
    let mut result = Vec::with_capacity(plan.pairs.len());
    result.extend(
        switches(permutation)
            .into_iter()
            .zip(plan.active)
            .filter_map(|(v, keep)| keep.then_some(v)),
    );
    result
}
