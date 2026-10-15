//! Dense lane and dyadic-chunk numbering controls for exactly corresponding components.
//! Offline experiments, not an adopted scheduler policy. No padding or changes
//! to input/output positions. The environment switches select explicit controls;
//! no compressed-size-based selection happens in the scheduler or encoder.
use super::{blocks, cmp_coordinates, graph, rebuild, signature, terms, Block, Graph, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{circuit::Circuit, FieldID};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

fn permutations(graph: &Graph, bs: &[Block]) -> Vec<Vec<u32>> {
    let mut by_component = BTreeMap::<usize, Vec<&Block>>::new();
    let mut rank = vec![u32::MAX; graph.components.len()];
    let mut lookup = HashMap::new();
    for b in bs {
        by_component.entry(b.component).or_default().push(b);
        lookup.insert((b.component, b.depth), b);
        for (r, &g) in b.outputs.iter().enumerate() {
            rank[graph.offsets[b.depth + 1] + g as usize] = r as u32;
        }
    }
    // Match complete local DAGs, including boundary types/constant values and
    // connections to preceding-layer outputs. No size threshold or source tags.
    let mut families = HashMap::<Vec<u32>, Vec<usize>>::new();
    for (&component, blocks) in &by_component {
        let mut key = Vec::new();
        for b in blocks {
            let s = signature(b);
            key.push(s.len() as u32);
            key.extend(s);
            for &h in b.inputs.iter().skip(b.ports.len()) {
                key.push(rank[graph.offsets[b.depth] + h as usize]);
            }
        }
        families.entry(key).or_default().push(component);
    }
    let repeated = families.values().filter(|v| v.len() > 1).count();
    let translated_only = std::env::var_os("MORTON_LANE_TRANSLATED_ONLY").is_some();
    let mut eligible = 0;
    let mut cohorts = Vec::<Vec<usize>>::new();
    for family in families.values() {
        if translated_only
            && !family.iter().skip(1).all(|&component| {
                by_component[&family[0]]
                    .iter()
                    .zip(&by_component[&component])
                    .all(|(a, b)| {
                        a.outputs.iter().zip(&b.outputs).all(|(&g, &h)| {
                            h.wrapping_sub(g) == b.outputs[0].wrapping_sub(a.outputs[0])
                        })
                    })
            })
        {
            continue;
        }
        if family.len() > 1 {
            eligible += 1;
        }
        let mut first = 0;
        while family.len() - first >= 2 {
            let size = 1usize << ((usize::BITS - 1) - (family.len() - first).leading_zeros());
            cohorts.push(family[first..first + size].to_vec());
            first += size;
        }
    }
    // Descending powers of two guarantee aligned bases without holes: every
    // previously placed block length is divisible by the next cohort width.
    cohorts.sort_by_key(|v| (std::cmp::Reverse(v.len()), v[0]));
    let mut maps: Vec<Vec<u32>> = graph
        .counts
        .iter()
        .map(|&n| (0..n as u32).collect())
        .collect();
    let mut placed = 0usize;
    let dyadic = std::env::var_os("MORTON_DYADIC_CHUNKS").is_some();
    let in_place = dyadic || std::env::var_os("MORTON_LANE_IN_PLACE").is_some();
    let mut chunk_sizes = BTreeMap::<usize, usize>::new();
    let mut aligned_wires = 0usize;
    let mut fringe_wires = 0usize;
    let mut widths = BTreeMap::<usize, usize>::new();
    for group in &cohorts {
        *widths.entry(group.len()).or_default() += 1;
    }
    // Inputs and final outputs retain their original public-facing numbering.
    for d in 0..graph.counts.len() - 2 {
        if d == 0 && std::env::var_os("MORTON_LANE_KEEP_FIRST").is_some() {
            continue;
        }
        let map = &mut maps[d + 1];
        if !in_place {
            map.fill(u32::MAX);
        }
        let mut cursor = 0;
        for group in &cohorts {
            let Some(first) = lookup.get(&(group[0], d)) else {
                continue;
            };
            let p = group.len();
            if !in_place {
                assert_eq!(cursor % p, 0);
            }
            let members: Vec<_> = group.iter().map(|&c| lookup[&(c, d)]).collect();
            assert!(members
                .iter()
                .all(|b| b.outputs.len() == first.outputs.len()));
            let mut slots = Vec::new();
            if dyadic {
                let mut available: Vec<_> = members
                    .iter()
                    .flat_map(|b| b.outputs.iter().copied())
                    .collect();
                available.sort_unstable();
                let mut pool = BTreeMap::<usize, BTreeSet<u32>>::new();
                let mut i = 0;
                while i < available.len() {
                    let mut end = i + 1;
                    while end < available.len() && available[end] == available[end - 1] + 1 {
                        end += 1;
                    }
                    while i < end {
                        let size = 1usize
                            << ((usize::BITS - 1 - (end - i).leading_zeros())
                                .min(available[i].trailing_zeros()));
                        pool.entry(size).or_default().insert(available[i]);
                        i += size;
                    }
                }
                let mut local = 0;
                while local < first.outputs.len() {
                    let mut size =
                        1usize << (usize::BITS - 1 - (first.outputs.len() - local).leading_zeros());
                    while pool
                        .range(size..)
                        .map(|(&s, v)| v.len() * (s / size))
                        .sum::<usize>()
                        < p
                    {
                        size /= 2;
                    }
                    assert!(size > 0);
                    *chunk_sizes.entry(size).or_default() += p;
                    for b in &members {
                        let mut allocated = *pool
                            .range(size..)
                            .filter(|(_, v)| !v.is_empty())
                            .min_by_key(|(_, v)| v.first().copied().unwrap())
                            .unwrap()
                            .0;
                        let base = pool.get_mut(&allocated).unwrap().pop_first().unwrap();
                        while allocated > size {
                            allocated /= 2;
                            pool.entry(allocated)
                                .or_default()
                                .insert(base + allocated as u32);
                        }
                        assert_eq!(base as usize % size, 0);
                        for offset in 0..size {
                            map[b.outputs[local + offset] as usize] = base + offset as u32;
                        }
                    }
                    local += size;
                }
                assert!(pool.values().all(BTreeSet::is_empty));
                placed += available.len();
                continue;
            }
            if in_place {
                let mut available: Vec<_> = members
                    .iter()
                    .flat_map(|b| b.outputs.iter().copied())
                    .collect();
                available.sort_unstable();
                let mut fringe = Vec::new();
                let mut i = 0;
                while i < available.len() {
                    let g = available[i];
                    if (g as usize).is_multiple_of(p)
                        && i + p <= available.len()
                        && available[i + p - 1] == g + p as u32 - 1
                    {
                        slots.extend_from_slice(&available[i..i + p]);
                        i += p;
                    } else {
                        fringe.push(g);
                        i += 1;
                    }
                }
                aligned_wires += slots.len();
                fringe_wires += fringe.len();
                slots.extend(fringe);
                assert_eq!(slots.len(), first.outputs.len() * p);
            }
            for local in 0..first.outputs.len() {
                for (lane, b) in members.iter().enumerate() {
                    let old = b.outputs[local] as usize;
                    if in_place {
                        map[old] = slots[local * p + lane];
                    } else {
                        assert_eq!(map[old], u32::MAX);
                        map[old] = (cursor + local * p + lane) as u32;
                    }
                }
            }
            let n = first.outputs.len() * p;
            cursor += n;
            placed += n;
        }
        // Unmatched residual wires retain their relative original ordering.
        if !in_place {
            for slot in map.iter_mut() {
                if *slot == u32::MAX {
                    *slot = cursor as u32;
                    cursor += 1;
                }
            }
            assert_eq!(cursor, map.len());
        }
        let mut seen = vec![false; map.len()];
        for &g in map.iter() {
            assert!(!seen[g as usize]);
            seen[g as usize] = true;
        }
    }
    println!(
        "LANES exact_families={repeated} eligible_families={eligible} translated_only={translated_only} cohorts={} widths={widths:?} interleaved_internal_wires={placed} in_place={in_place} dyadic={dyadic} chunk_sizes={chunk_sizes:?} aligned_wires={aligned_wires} fringe_wires={fringe_wires} padding=0 inputs_fixed=true outputs_fixed=true",
        cohorts.len()
    );
    maps
}

fn relabel<F: SerializableField>(
    f: &F,
    c: &Circuit<F>,
    ts: &[Vec<T>],
    maps: &[Vec<u32>],
) -> Circuit<F> {
    let coefficients: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut layers = Vec::new();
    for (d, ts) in ts.iter().enumerate() {
        let mut renamed: Vec<_> = ts
            .iter()
            .map(|t| {
                let a = maps[d][t[1] as usize];
                let b = maps[d][t[2] as usize];
                [maps[d + 1][t[0] as usize], a.min(b), a.max(b), t[3]]
            })
            .collect();
        renamed.sort_unstable_by(|a, b| {
            cmp_coordinates(a, b)
                .then_with(|| coefficients[a[3] as usize].cmp(&coefficients[b[3] as usize]))
        });
        layers.push(renamed);
    }
    rebuild(f, c, layers)
}

pub(super) fn lane_order<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
) -> Circuit<F> {
    let ts = terms(c);
    let graph = graph(f, c, &ts);
    let bs = blocks(&graph, &ts, false);
    let maps = permutations(&graph, &bs);
    let renamed = relabel(f, c, &ts, &maps);
    let inverse: Vec<Vec<u32>> = maps
        .iter()
        .map(|map| {
            let mut inv = vec![0; map.len()];
            for (old, &new) in map.iter().enumerate() {
                inv[new as usize] = old as u32;
            }
            inv
        })
        .collect();
    let restored = relabel(f, c, &terms(&renamed), &inverse);
    let writer = core_proto::writer::CircuitWriter::new(f, FieldID::None);
    assert_eq!(writer.to_bytes_lfc1(&restored), writer.to_bytes_lfc1(c));
    println!(
        "LANE_CORRECTNESS exact_inverse_lfc1=true original_id={:02x?} new_id={:02x?}",
        c.id, renamed.id
    );
    renamed
}

pub(super) fn memory<F: SerializableField>(label: &str, c: &Circuit<F>) {
    let d: usize = c.raw.layers.iter().map(|l| l.deltas().len()).sum();
    let segments: usize = c.raw.layers.iter().map(|l| l.delta_segments().len()).sum();
    let entries: usize = c
        .raw
        .layers
        .iter()
        .flat_map(|l| l.delta_segments())
        .map(Vec::len)
        .sum();
    let tokens: usize = c.raw.layers.iter().map(|l| l.delta_tokens().len()).sum();
    let payload = d * std::mem::size_of::<core_proto::TermDelta>()
        + (entries + tokens) * 4
        + segments * std::mem::size_of::<Vec<u32>>();
    println!(
        "MEMORY {label}: deltas={d} segments={segments} segment_entries={entries} tokens={tokens} payload_and_segment_headers_bytes={payload} excludes_capacity_slack_constants_and_allocator_overhead=true"
    );
}

pub(super) fn analyze<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    field_id: FieldID,
) {
    let renamed = lane_order(f, c);
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    for (label, circuit) in [("original", c), ("lane_order", &renamed)] {
        let mut unique = HashSet::new();
        for l in &circuit.raw.layers {
            l.for_each_delta(|&d| {
                unique.insert(d);
            });
        }
        println!("LANE_DELTAS {label}: global={}", unique.len());
        let stats_only = std::env::var_os("MORTON_LANE_STATS_ONLY").is_some();
        if !stats_only {
            super::sizes(&format!("{label}_lfc1"), &writer.to_bytes_lfc1(circuit));
            super::sizes(
                &format!("{label}_lfc2_native"),
                &writer.to_bytes_lfc2(circuit),
            );
        }
        let segmented = compile_compiler::segment_circuit(f, circuit);
        if stats_only {
            for (depth, l) in segmented.raw.layers.iter().rev().enumerate() {
                let mut body = Vec::new();
                super::put(&mut body, l.logw() as u32);
                super::put(&mut body, l.nw() as u32);
                super::put(&mut body, l.deltas().len() as u32);
                for t in l.deltas() {
                    for n in [
                        super::zig(t.g),
                        super::zig(t.h[0]),
                        super::zig(t.h[1]),
                        t.k_index,
                    ] {
                        super::put(&mut body, n);
                    }
                }
                super::put(&mut body, l.delta_segments().len() as u32);
                for s in l.delta_segments() {
                    super::put(&mut body, s.len() as u32);
                    for &n in s {
                        super::put(&mut body, n);
                    }
                }
                super::put(&mut body, l.delta_tokens().len() as u32);
                for &n in l.delta_tokens() {
                    super::put(&mut body, n);
                }
                println!(
                    "LAYER {label} depth={} terms={} deltas={} lfc2_body={} independent_zstd16={}",
                    depth + 1,
                    l.num_terms(),
                    l.deltas().len(),
                    body.len(),
                    zstd::bulk::compress(&body, 16).unwrap().len()
                );
            }
            memory(label, &segmented);
            continue;
        }
        super::sizes(
            &format!("{label}_lfc2_segmented"),
            &writer.to_bytes_lfc2(&segmented),
        );
        memory(label, &segmented);
        let bytes = writer.to_bytes_lfc2(&segmented);
        let (decoded, tail) = core_proto::reader::CircuitReader::new(f, field_id)
            .from_bytes_lfc2(&bytes, true)
            .unwrap();
        assert!(tail.is_empty());
        assert_eq!(
            writer.to_bytes_lfc1(&decoded),
            writer.to_bytes_lfc1(circuit)
        );
        println!("LANE_LFC2_ROUNDTRIP {label}: exact=true");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn power_two_low_lanes_do_not_change_local_morton_comparison() {
        for p in [2u32, 4, 8, 16] {
            for a in 0..8 {
                for b in 0..8 {
                    for x in 0..8 {
                        for y in 0..8 {
                            let local = cmp_coordinates(&[0, a, b, 0], &[0, x, y, 0]);
                            if local.is_eq() {
                                continue;
                            }
                            for c in 0..p {
                                for d in 0..p {
                                    assert_eq!(
                                        cmp_coordinates(
                                            &[0, a * p + c, b * p + c, 0],
                                            &[0, x * p + d, y * p + d, 0]
                                        ),
                                        local
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
