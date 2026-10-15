// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Offline template-guided bijections of internal layer wires. Ordinary LFC2 only.
//! Original inputs and final outputs are fixed. No padding or runtime maps.
use super::{blocks, graph, rebuild, signature, terms, Block, Graph, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::circuit::Circuit;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Exact full-DAG families, not just independently matching layer programs.
/// Include the local rank of every internal input in the preceding output map.
fn whole_families(gr: &Graph, bs: &[Block]) -> Vec<Vec<usize>> {
    let mut rank = vec![u32::MAX; gr.components.len()];
    let mut components = BTreeMap::<usize, Vec<&Block>>::new();
    for b in bs {
        components.entry(b.component).or_default().push(b);
        for (i, &g) in b.outputs.iter().enumerate() {
            rank[gr.offsets[b.depth + 1] + g as usize] = i as u32;
        }
    }
    let mut keys = HashMap::<Vec<u32>, usize>::new();
    let mut families = Vec::<Vec<usize>>::new();
    for (&component, blocks) in &components {
        // Constants are shared ports, not members of ordinary component families.
        if gr.constants[component].is_some() {
            continue;
        }
        let mut key = Vec::new();
        for b in blocks {
            let s = signature(b);
            key.push(s.len() as u32);
            key.extend(s);
            for &h in b.inputs.iter().skip(b.ports.len()) {
                let r = rank[gr.offsets[b.depth] + h as usize];
                assert_ne!(r, u32::MAX);
                key.push(r);
            }
        }
        let next = families.len();
        let id = *keys.entry(key).or_insert_with(|| {
            families.push(Vec::new());
            next
        });
        families[id].push(component);
    }
    // BTreeMap visitation made families and instances deterministic, ordered by
    // the minimum original global wire ID. HashMap iteration never sets layout.
    families
}

fn permutations(gr: &Graph, bs: &[Block], policy: &str) -> Vec<Vec<u32>> {
    assert!(matches!(
        policy,
        "whole" | "layer" | "role" | "role4" | "role16"
    ));
    let families = whole_families(gr, bs);
    let lookup: HashMap<_, _> = bs.iter().map(|b| ((b.component, b.depth), b)).collect();
    let mut maps: Vec<Vec<u32>> = gr.counts.iter().map(|&n| (0..n as u32).collect()).collect();
    let mut packed = 0;
    for d in 1..maps.len() - 1 {
        let mut order = Vec::with_capacity(maps[d].len());
        // Keep equal-valued constant ports adjacent, outside ordinary instances.
        let mut constants: Vec<_> = (0..gr.counts[d] as u32)
            .filter(|&g| gr.constants[gr.offsets[d] + g as usize].is_some())
            .collect();
        constants.sort_unstable_by_key(|&g| (gr.constants[gr.offsets[d] + g as usize], g));
        order.extend(constants);
        if policy == "whole" {
            for family in &families {
                for &component in family {
                    if let Some(b) = lookup.get(&(component, d - 1)) {
                        order.extend(&b.outputs);
                        packed += b.outputs.len();
                    }
                }
            }
        } else if policy.starts_with("role") {
            let tile = match policy {
                "role" => 1,
                "role4" => 4,
                "role16" => 16,
                _ => unreachable!(),
            };
            for family in &families {
                let blocks: Vec<_> = family
                    .iter()
                    .filter_map(|&component| lookup.get(&(component, d - 1)).copied())
                    .collect();
                if let Some(first) = blocks.first() {
                    assert!(blocks
                        .iter()
                        .all(|b| b.outputs.len() == first.outputs.len()));
                    for start in (0..first.outputs.len()).step_by(tile) {
                        let end = (start + tile).min(first.outputs.len());
                        for b in &blocks {
                            order.extend(&b.outputs[start..end]);
                            packed += end - start;
                        }
                    }
                }
            }
        } else {
            let mut keys = HashMap::<Vec<u32>, usize>::new();
            let mut groups = Vec::<Vec<&Block>>::new();
            for b in bs
                .iter()
                .filter(|b| b.depth + 1 == d && gr.constants[b.component].is_none())
            {
                let next = groups.len();
                let id = *keys.entry(signature(b)).or_insert_with(|| {
                    groups.push(Vec::new());
                    next
                });
                groups[id].push(b);
            }
            for group in groups {
                for b in group {
                    order.extend(&b.outputs);
                    packed += b.outputs.len();
                }
            }
        }
        assert_eq!(order.len(), maps[d].len());
        maps[d].fill(u32::MAX);
        for (new, old) in order.into_iter().enumerate() {
            assert_eq!(maps[d][old as usize], u32::MAX, "duplicate wire placement");
            maps[d][old as usize] = new as u32;
        }
    }
    let changed: usize = maps
        .iter()
        .map(|m| {
            m.iter()
                .enumerate()
                .filter(|&(i, &j)| i != j as usize)
                .count()
        })
        .sum();
    println!("WIRE_LAYOUT policy={policy} repeated_whole_families={} packed_internal_wires={packed} renamed_wires={changed} inputs_fixed=true outputs_fixed=true padding=0",
        families.iter().filter(|f|f.len()>1).count());
    maps
}

fn inverse(maps: &[Vec<u32>]) -> Vec<Vec<u32>> {
    maps.iter()
        .map(|map| {
            let mut inverse = vec![u32::MAX; map.len()];
            for (old, &new) in map.iter().enumerate() {
                assert!((new as usize) < map.len());
                assert_eq!(inverse[new as usize], u32::MAX, "non-bijective wire map");
                inverse[new as usize] = old as u32;
            }
            inverse
        })
        .collect()
}

fn relabel(ts: &[Vec<T>], maps: &[Vec<u32>]) -> Vec<Vec<T>> {
    ts.iter()
        .enumerate()
        .map(|(d, layer)| {
            layer
                .iter()
                .map(|t| {
                    let a = maps[d][t[1] as usize];
                    let b = maps[d][t[2] as usize];
                    [maps[d + 1][t[0] as usize], a.min(b), a.max(b), t[3]]
                })
                .collect()
        })
        .collect()
}

// Measure exact interior delta reuse for known corresponding layer programs.
// Each sequence has the same local shape-first traversal; omit only its first
// boundary delta. This separates relabeling from global traversal/segmentation.
fn repetition(gr: &Graph, bs: &[Block], maps: &[Vec<u32>], label: &str) {
    let mut groups = HashMap::<Vec<u32>, Vec<&Block>>::new();
    for b in bs {
        groups.entry(signature(b)).or_default().push(b);
    }
    let mut instances = 0;
    let mut terms = 0;
    let mut distinct = 0;
    let mut repeated = 0;
    let mut translated_outputs = 0;
    let mut translated_inputs = 0;
    let mut compared = 0;
    for group in groups.values().filter(|g| g.len() > 1) {
        let mut sequences = HashSet::new();
        let first = group[0];
        let translated = |a: &[u32], b: &[u32], map: &[u32]| {
            a.len() == b.len()
                && a.first().is_none_or(|&x| {
                    let delta = map[b[0] as usize].wrapping_sub(map[x as usize]);
                    a.iter()
                        .zip(b)
                        .all(|(&x, &y)| map[y as usize].wrapping_sub(map[x as usize]) == delta)
                })
        };
        for b in group {
            compared += 1;
            translated_outputs +=
                usize::from(translated(&first.outputs, &b.outputs, &maps[b.depth + 1]));
            // Internal input maps: ports (including original inputs) excluded.
            translated_inputs += usize::from(translated(
                &first.inputs[first.ports.len()..],
                &b.inputs[b.ports.len()..],
                &maps[b.depth],
            ));
            let mut local = b.local.clone();
            let kind = |t: &T| {
                shape(
                    gr,
                    b.depth,
                    b.inputs[t[1] as usize],
                    b.inputs[t[2] as usize],
                )
            };
            local.sort_unstable_by_key(|t| {
                (
                    kind(t),
                    std::cmp::Reverse(t[0]),
                    std::cmp::Reverse(t[2]),
                    t[1],
                    t[3],
                )
            });
            for k in 0..4 {
                let seq: Vec<_> = local
                    .iter()
                    .filter(|t| kind(t) == k)
                    .map(|t| {
                        let a = maps[b.depth][b.inputs[t[1] as usize] as usize];
                        let h = maps[b.depth][b.inputs[t[2] as usize] as usize];
                        [
                            maps[b.depth + 1][b.outputs[t[0] as usize] as usize],
                            a.min(h),
                            a.max(h),
                            t[3],
                        ]
                    })
                    .collect();
                if seq.len() < 2 {
                    continue;
                }
                let ds = super::deltas(&seq)[1..].to_vec();
                instances += 1;
                terms += ds.len();
                if !sequences.insert((k, ds)) {
                    repeated += 1;
                }
            }
        }
        distinct += sequences.len();
    }
    println!("WIRE_REPETITION label={label} shape_instances={instances} interior_terms={terms} distinct_sequences={distinct} duplicate_sequences={repeated} compared_blocks={compared} translated_output_maps={translated_outputs} translated_internal_input_maps={translated_inputs}");
}

fn shape(gr: &Graph, d: usize, a: u32, b: u32) -> u8 {
    match (
        gr.constants[gr.offsets[d] + a as usize] == gr.constants[0],
        gr.constants[gr.offsets[d] + b as usize] == gr.constants[0],
    ) {
        (true, true) => 0,
        (true, false) | (false, true) => 1,
        (false, false) if a == b => 2,
        _ => 3,
    }
}

pub fn renumber<F: AlgebraicField + SerializableField>(
    f: &F,
    c: &Circuit<F>,
    policy: &str,
) -> Circuit<F> {
    renumber_with_maps(f, c, policy).0
}

pub fn renumber_with_maps<F: AlgebraicField + SerializableField>(
    f: &F,
    c: &Circuit<F>,
    policy: &str,
) -> (Circuit<F>, Vec<Vec<u32>>) {
    let ts = terms(c);
    let gr = graph(f, c, &ts);
    let bs = blocks(&gr, &ts, false);
    // Do not silently drop geometrical wires that happen to be absent from terms.
    let expected: Vec<_> = std::iter::once(c.raw.ninput)
        .chain(c.raw.layers.iter().rev().skip(1).map(|l| l.nw()))
        .chain(std::iter::once(c.raw.noutput))
        .collect();
    assert_eq!(gr.counts, expected);
    let maps = permutations(&gr, &bs, policy);
    for &d in &[0, maps.len() - 1] {
        assert!(maps[d].iter().enumerate().all(|(i, &j)| i == j as usize));
    }
    let identity: Vec<_> = gr.counts.iter().map(|&n| (0..n as u32).collect()).collect();
    repetition(&gr, &bs, &identity, "original");
    repetition(&gr, &bs, &maps, policy);
    let renamed = relabel(&ts, &maps);
    let restored = relabel(&renamed, &inverse(&maps));
    for (mut before, mut after) in ts.into_iter().zip(restored) {
        for t in &mut before {
            if t[1] > t[2] {
                t.swap(1, 2);
            }
        }
        before.sort_unstable();
        after.sort_unstable();
        assert_eq!(before, after);
    }
    println!("WIRE_CORRECTNESS inverse_term_multiset=true constants_unchanged=true");
    (rebuild(f, c, renamed), maps)
}

/// Same global shape-first comparator as the current policy, without imposing
/// any requirement on the source traversal. Used to isolate wire numbering.
pub fn shape_order<F: AlgebraicField + SerializableField>(f: &F, c: &Circuit<F>) -> Circuit<F> {
    let mut ts = terms(c);
    let gr = graph(f, c, &ts);
    let coefficients: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    for (d, layer) in ts.iter_mut().enumerate() {
        layer.sort_unstable_by(|a, b| {
            shape(&gr, d, a[1], a[2])
                .cmp(&shape(&gr, d, b[1], b[2]))
                .then(b[0].cmp(&a[0]))
                .then(b[2].cmp(&a[2]))
                .then(a[1].cmp(&b[1]))
                .then_with(|| coefficients[a[3] as usize].cmp(&coefficients[b[3] as usize]))
        });
    }
    rebuild(f, c, ts)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn corresponding_components_get_translated_internal_maps() {
        use core_proto::circuit::RawCircuit;
        let f = compile_algebra::gf2_128::Gf2_128Field::new();
        let c = Circuit {
            raw: RawCircuit {
                ninput: 5,
                npublic_input: 1,
                noutput: 2,
                logv: 1,
                subfield_boundary: 0,
                constants: vec![f.one()],
                layers: Vec::new(),
            },
            id: [0; 32],
        };
        // Two identical DAGs have interleaved first-layer outputs. Shared one
        // is copied through both internal layers, without connecting the DAGs.
        let ts = vec![
            vec![
                [0, 0, 0, 0],
                [1, 1, 1, 0],
                [2, 3, 3, 0],
                [3, 2, 2, 0],
                [4, 4, 4, 0],
            ],
            vec![
                [0, 0, 0, 0],
                [1, 1, 3, 0],
                [1, 0, 1, 0],
                [2, 2, 4, 0],
                [2, 0, 2, 0],
            ],
            vec![[0, 1, 1, 0], [1, 2, 2, 0]],
        ];
        let gr = graph(&f, &c, &ts);
        let bs = blocks(&gr, &ts, false);
        let families = whole_families(&gr, &bs);
        assert_eq!(families.iter().filter(|f| f.len() > 1).count(), 1);
        for policy in ["whole", "layer", "role", "role4", "role16"] {
            let maps = permutations(&gr, &bs, policy);
            assert_eq!(maps[0], vec![0, 1, 2, 3, 4]);
            assert_eq!(maps[1], if policy == "role" { vec![0, 1, 2, 3, 4] } else { vec![0, 1, 3, 2, 4] });
            assert_eq!(maps[2], vec![0, 1, 2]);
            assert_eq!(maps[3], vec![0, 1]);
            let renamed = relabel(&ts, &maps);
            assert_eq!(relabel(&renamed, &inverse(&maps)), ts);
            // Exactly corresponding terms now have identical interior strides.
            assert_eq!(maps[1][2] - maps[1][1], maps[1][4] - maps[1][3]);
            let evaluate = |layers: &[Vec<T>]| {
                let mut values = vec![1u64, 2, 3, 5, 7];
                for (d, layer) in layers.iter().enumerate() {
                    let mut next = vec![0; gr.counts[d + 1]];
                    for t in layer {
                        next[t[0] as usize] += values[t[1] as usize] * values[t[2] as usize];
                    }
                    values = next;
                }
                values
            };
            assert_eq!(evaluate(&ts), evaluate(&renamed));
        }
    }

    #[test]
    fn inverse_preserves_terms_and_duplicates() {
        let maps = vec![vec![0, 1, 2], vec![2, 0, 1], vec![0]];
        let ts = vec![
            vec![[0, 1, 2, 1], [0, 1, 2, 1], [2, 0, 1, 0]],
            vec![[0, 0, 2, 1]],
        ];
        assert_eq!(relabel(&relabel(&ts, &maps), &inverse(&maps)), ts);
    }
    #[test]
    #[should_panic(expected = "non-bijective")]
    fn duplicate_map_rejected() {
        inverse(&[vec![0, 0]]);
    }
}
