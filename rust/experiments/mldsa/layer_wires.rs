//! Offline, invertible layer-wire layout controls. Never add wires or padding.
use super::{cmp_coordinates, graph, rebuild, terms, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::circuit::Circuit;

fn assign(map: &mut [u32], mut order: Vec<usize>, one: &[bool], placement: &str) {
    let (placement, swap) = placement
        .strip_prefix("swap_")
        .map_or((placement, false), |p| (p, true));
    let nc = order.iter().filter(|&&g| one[g]).count();
    let ordinary = order.len() - nc;
    let msb = if map.is_empty() {
        0
    } else {
        1usize << map.len().ilog2()
    };
    let position = match placement {
        "first" => 0,
        "last" => ordinary,
        "msb" => msb,
        "before_msb" => msb.saturating_sub(1),
        "middle" => map.len() / 2,
        _ => panic!("Unknown constant placement {placement}"),
    }
    .min(ordinary);
    if swap {
        let target = position..position + nc;
        let sources: Vec<_> = order
            .iter()
            .enumerate()
            .filter_map(|(i, &g)| (one[g] && !target.contains(&i)).then_some(i))
            .collect();
        let destinations: Vec<_> = target.filter(|&i| !one[order[i]]).collect();
        assert_eq!(sources.len(), destinations.len());
        for (a, b) in sources.into_iter().zip(destinations) {
            order.swap(a, b);
        }
    } else {
        let (constants, rest): (Vec<_>, Vec<_>) = order.into_iter().partition(|&g| one[g]);
        order = rest;
        order.splice(position..position, constants);
    }
    for (new, old) in order.into_iter().enumerate() {
        map[old] = new as u32;
    }
}

pub(in super::super) fn reorder<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    policy: &str,
) -> Circuit<F> {
    assert!(
        !policy.starts_with("input_"),
        "All circuit input IDs must remain fixed"
    );
    let ts = terms(c);
    let graph = graph(f, c, &ts);
    let n = ts.len();
    let mut maps: Vec<Vec<u32>> = graph
        .counts
        .iter()
        .map(|&n| (0..n as u32).collect())
        .collect();
    let ones: Vec<Vec<bool>> = graph
        .counts
        .iter()
        .enumerate()
        .map(|(d, &n)| {
            graph.constants[graph.offsets[d]..graph.offsets[d] + n]
                .iter()
                .map(|&x| x == graph.constants[0])
                .collect()
        })
        .collect();
    let coeffs: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut ko: Vec<_> = (0..coeffs.len()).collect();
    ko.sort_by_key(|&k| &coeffs[k]);
    let mut kr = vec![0; ko.len()];
    for (r, &k) in ko.iter().enumerate() {
        kr[k] = r as u32;
    }
    let (base, placement) = policy.split_once("_one_").unwrap_or((policy, "first"));
    let bit_policy = ["rotate", "bitrev", "xor"].into_iter().find_map(|kind| {
        base.strip_prefix(kind)
            .map(|bits| (kind, bits.parse::<u32>().unwrap()))
    });
    if let Some((kind, bits)) = bit_policy {
        assert!((1..=16).contains(&bits));
        let block = 1u32 << bits;
        for map in &mut maps[1..n] {
            let complete = map.len() as u32 / block * block;
            for old in 0..complete {
                let x = old & (block - 1);
                let y = match kind {
                    "rotate" => ((x << 1) | (x >> (bits - 1))) & (block - 1),
                    "bitrev" => x.reverse_bits() >> (32 - bits),
                    "xor" => x ^ (block - 1),
                    _ => unreachable!(),
                };
                map[old as usize] = (old & !(block - 1)) | y;
            }
        }
    }
    let (group, method) = if bit_policy.is_some() {
        ("global", "identity")
    } else if let Some(m) = base.strip_prefix("bip1_") {
        ("bip1", m)
    } else if let Some(m) = base.strip_prefix("bip0_") {
        ("bip0", m)
    } else if let Some(m) = base.strip_prefix("whole_") {
        ("whole", m)
    } else {
        ("global", base)
    };
    assert!([
        "identity", "old", "reverse", "degree", "first", "last", "bary", "bary3", "median",
        "median3", "minmax", "fanin", "shape", "morton"
    ]
    .contains(&method));
    let rounds = if method.ends_with('3') { 3 } else { 1 };
    for _ in 0..rounds {
        if method == "identity" && placement != "first" {
            for d in 1..n {
                let order = (0..graph.counts[d]).collect();
                assign(&mut maps[d], order, &ones[d], placement);
            }
        }
        if method != "identity" {
            for d in 0..n - 1 {
                let mut adjacency = vec![Vec::<u32>::new(); graph.counts[d + 1]];
                let mut fanins = vec![Vec::<[u32; 3]>::new(); graph.counts[d + 1]];
                let mut layer = Vec::with_capacity(ts[d].len());
                for t in &ts[d] {
                    let g = t[0] as usize;
                    let a = maps[d][t[1] as usize];
                    let b = maps[d][t[2] as usize];
                    layer.push([t[0], a.min(b), a.max(b), t[3]]);
                    fanins[g].push([a.min(b), a.max(b), kr[t[3] as usize]]);
                    for h in [t[1], t[2]] {
                        if !ones[d][h as usize] {
                            adjacency[g].push(maps[d][h as usize]);
                        }
                    }
                }
                for hs in &mut adjacency {
                    hs.sort_unstable();
                    hs.dedup();
                }
                for (g, fan) in fanins.iter_mut().enumerate() {
                    if method == "shape" {
                        for t in fan.iter_mut() {
                            for h in &mut t[..2] {
                                *h = adjacency[g].binary_search(h).map_or(0, |i| i as u32 + 1);
                            }
                            if t[1] < t[0] {
                                t.swap(0, 1);
                            }
                        }
                    }
                    if method == "first" || method == "last" {
                        fan.sort_unstable_by_key(|t| (super::interleave(&t[..2], 1), t[2]));
                    } else {
                        fan.sort_unstable();
                    }
                }
                let scores: Vec<_> = adjacency
                    .iter()
                    .map(|hs| {
                        let sum: u64 = hs.iter().map(|&h| u64::from(h)).sum();
                        let len = hs.len().max(1) as u64;
                        let lo = hs.first().copied().unwrap_or(0);
                        let hi = hs.last().copied().unwrap_or(0);
                        let med = hs.get(hs.len() / 2).copied().unwrap_or(0);
                        (sum, len, lo, hi, med)
                    })
                    .collect();
                let ranks = match group {
                    "global" => vec![0; graph.counts[d + 1]],
                    "whole" => (0..graph.counts[d + 1])
                        .map(|g| graph.components[graph.offsets[d + 1] + g])
                        .collect(),
                    "bip1" | "bip0" => {
                        let mut input_one = vec![false; graph.counts[d]];
                        for (h, &new) in maps[d].iter().enumerate() {
                            input_one[new as usize] = ones[d][h];
                        }
                        super::super::bipartite::partition_with_order(
                            &layer,
                            graph.counts[d],
                            graph.counts[d + 1],
                            &input_one,
                            &ones[d + 1],
                            group == "bip1",
                            true,
                        )
                        .output_rank
                    }
                    _ => unreachable!(),
                };
                let mut order: Vec<_> = (0..graph.counts[d + 1]).collect();
                order.sort_unstable_by(|&a, &b| {
                    ranks[a].cmp(&ranks[b]).then_with(|| {
                        let x = scores[a];
                        let y = scores[b];
                        match method {
                            "old" => a.cmp(&b),
                            "reverse" => b.cmp(&a),
                            "degree" => adjacency[a].len().cmp(&adjacency[b].len()),
                            "first" | "last" => {
                                let key = |i: usize| {
                                    let t = if method == "first" {
                                        fanins[i].first()
                                    } else {
                                        fanins[i].last()
                                    };
                                    t.map(|t| (super::interleave(&t[..2], 1), t[2]))
                                };
                                key(a).cmp(&key(b))
                            }
                            "bary" | "bary3" => (u128::from(x.0) * u128::from(y.1))
                                .cmp(&(u128::from(y.0) * u128::from(x.1))),
                            "median" | "median3" => x.4.cmp(&y.4),
                            "minmax" => (x.2, x.3).cmp(&(y.2, y.3)),
                            "morton" => super::interleave(&[x.2, x.3], 1)
                                .cmp(&super::interleave(&[y.2, y.3], 1)),
                            "fanin" | "shape" => fanins[a].cmp(&fanins[b]),
                            _ => unreachable!(),
                        }
                        .then(x.2.cmp(&y.2))
                        .then(x.3.cmp(&y.3))
                        .then(a.cmp(&b))
                    })
                });
                assign(&mut maps[d + 1], order, &ones[d + 1], placement);
            }
        }
        if rounds > 1 {
            // Reverse sweep: order intermediate inputs by their consumer positions.
            for d in (1..n).rev() {
                let mut adjacency = vec![Vec::<u32>::new(); graph.counts[d]];
                for t in &ts[d] {
                    for h in [t[1], t[2]] {
                        adjacency[h as usize].push(maps[d + 1][t[0] as usize]);
                    }
                }
                for hs in &mut adjacency {
                    hs.sort_unstable();
                    hs.dedup();
                }
                let scores: Vec<_> = adjacency
                    .iter()
                    .map(|h| {
                        (
                            h.iter().map(|&v| u64::from(v)).sum::<u64>(),
                            h.len().max(1) as u64,
                            h.get(h.len() / 2).copied().unwrap_or(0),
                        )
                    })
                    .collect();
                let mut order: Vec<_> = (0..graph.counts[d]).collect();
                order.sort_unstable_by(|&a, &b| {
                    let x = scores[a];
                    let y = scores[b];
                    (if method == "median3" {
                        x.2.cmp(&y.2)
                    } else {
                        (u128::from(x.0) * u128::from(y.1))
                            .cmp(&(u128::from(y.0) * u128::from(x.1)))
                    })
                    .then(a.cmp(&b))
                });
                assign(&mut maps[d], order, &ones[d], placement);
            }
        }
    }
    let inverse: Vec<Vec<u32>> = maps
        .iter()
        .map(|map| {
            let mut inv = vec![u32::MAX; map.len()];
            for (old, &new) in map.iter().enumerate() {
                assert_eq!(inv[new as usize], u32::MAX);
                inv[new as usize] = old as u32;
            }
            assert!(inv.iter().all(|&x| x != u32::MAX));
            inv
        })
        .collect();
    for (i, &new) in maps[0].iter().enumerate() {
        assert_eq!(new as usize, i, "Input wire {i} was renamed");
    }
    assert!(maps[n].iter().enumerate().all(|(i, &x)| i == x as usize));
    let apply = |layers: &[Vec<T>], m: &[Vec<u32>]| {
        layers
            .iter()
            .enumerate()
            .map(|(d, l)| {
                let mut result: Vec<_> = l
                    .iter()
                    .map(|t| {
                        let a = m[d][t[1] as usize];
                        let b = m[d][t[2] as usize];
                        [m[d + 1][t[0] as usize], a.min(b), a.max(b), t[3]]
                    })
                    .collect();
                result.sort_unstable_by(|a, b| {
                    cmp_coordinates(a, b)
                        .then_with(|| coeffs[a[3] as usize].cmp(&coeffs[b[3] as usize]))
                });
                result
            })
            .collect::<Vec<_>>()
    };
    let rewired = apply(&ts, &maps);
    assert_eq!(apply(&rewired, &inverse), ts);
    assert!(
        rewired[0]
            .iter()
            .zip(&ts[0])
            .all(|(a, b)| a[1..3] == b[1..3]),
        "Fixed circuit inputs must preserve the first layer's Morton input-pair stream"
    );
    let changes: usize = maps
        .iter()
        .map(|m| {
            m.iter()
                .enumerate()
                .filter(|&(i, &x)| i != x as usize)
                .count()
        })
        .sum();
    println!(
        "WIRE_LAYOUT {policy} moved={changes} exact_inverse=true all_inputs_and_external_outputs_fixed=true global_morton=true"
    );
    rebuild(f, c, rewired)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tiny() -> (
        compile_algebra::p256::P256Field,
        Circuit<compile_algebra::p256::P256Field>,
    ) {
        use compile_logic::{Logic, LogicIO};
        let f = compile_algebra::p256::P256Field::new();
        let (c, _, _) = compile_compiler::compile(&f, |logic| {
            let x = logic.input(1);
            let y = logic.input(2);
            let z = logic.mul(&x, &y);
            let z = logic.add(&z, &x);
            let z = logic.mul(&z, &y);
            (logic.assert0("result", &z), 1, 0)
        });
        (f, c)
    }

    #[test]
    #[should_panic(expected = "All circuit input IDs must remain fixed")]
    fn input_renumbering_is_rejected() {
        let (f, c) = tiny();
        reorder(&f, &c, "input_identity");
    }

    #[test]
    fn legal_layouts_preserve_inputs_geometry_and_morton() {
        let (f, c) = tiny();
        for policy in [
            "identity",
            "bary3",
            "median3",
            "bip1_first",
            "bip0_fanin",
            "whole_shape",
            "identity_one_last",
            "identity_one_swap_last",
            "rotate2",
            "bitrev3",
            "xor2",
        ] {
            // reorder() checks full inverse, every input ID, external outputs,
            // and the invariant first-layer input-pair stream for each case.
            let result = reorder(&f, &c, policy);
            assert_eq!(result.raw.ninput, c.raw.ninput);
            assert_eq!(result.raw.noutput, c.raw.noutput);
            assert_eq!(result.raw.layers.len(), c.raw.layers.len());
            for (a, b) in result.raw.layers.iter().zip(&c.raw.layers) {
                assert_eq!(
                    (a.nw(), a.logw(), a.num_terms()),
                    (b.nw(), b.logw(), b.num_terms())
                );
            }
            assert!(terms(&result)
                .iter()
                .all(|l| l.windows(2).all(|w| !cmp_coordinates(&w[0], &w[1]).is_gt())));
        }
    }

    #[test]
    fn constant_placement_is_a_dense_permutation() {
        let one = [true, false, false, false, false, false, false];
        for (placement, expected) in [
            ("first", 0),
            ("last", 6),
            ("msb", 4),
            ("before_msb", 3),
            ("middle", 3),
        ] {
            let mut map = vec![u32::MAX; one.len()];
            assign(&mut map, (0..one.len()).collect(), &one, placement);
            assert_eq!(map[0], expected);
            let mut sorted = map.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..one.len() as u32).collect::<Vec<_>>());
            assert!(map[1..].windows(2).all(|w| w[0] < w[1]));
        }
    }

    #[test]
    fn all_one_and_no_one_layers_remain_permutations() {
        for one in [vec![true; 4], vec![false; 4]] {
            let mut map = vec![u32::MAX; 4];
            assign(&mut map, vec![3, 2, 1, 0], &one, "last");
            assert_eq!(map, [3, 2, 1, 0]);
        }
    }

    #[test]
    fn swapping_one_moves_only_two_wires() {
        let mut map = vec![u32::MAX; 7];
        assign(
            &mut map,
            (0..7).collect(),
            &[false, false, true, false, false, false, false],
            "swap_last",
        );
        assert_eq!(map, [0, 1, 6, 3, 4, 5, 2]);
    }
}
