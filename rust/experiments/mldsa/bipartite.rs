//! Offline per-layer bipartite component traversal and optional forward output packing.
use super::{cmp_coordinates, graph, rebuild, root, terms, union, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{circuit::Circuit, FieldID};
use std::collections::{BTreeMap, HashSet};
use std::time::Instant;

pub(super) struct Partition {
    pub(super) output_rank: Vec<usize>,
    components: usize,
    largest_outputs: usize,
    largest_terms: usize,
}

pub(super) fn layer_stats<F: SerializableField>(label: &str, c: &Circuit<F>) {
    for (d, l) in c.raw.layers.iter().rev().enumerate() {
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
            "BIPARTITE_BODY {label} depth={} deltas={} raw={} independent_zstd16={}",
            d + 1,
            l.deltas().len(),
            body.len(),
            zstd::bulk::compress(&body, 16).unwrap().len()
        );
    }
}

pub(super) fn partition_with_order(
    ts: &[T],
    ni: usize,
    no: usize,
    input_one: &[bool],
    output_one: &[bool],
    include_one: bool,
    input_first: bool,
) -> Partition {
    assert_eq!(input_one.len(), ni);
    assert_eq!(output_one.len(), no);
    let mut parent: Vec<_> = (0..ni + no).collect();
    for t in ts {
        let g = t[0] as usize;
        for h in [t[1] as usize, t[2] as usize] {
            if include_one || (!input_one[h] && !output_one[g]) {
                union(&mut parent, h, ni + g);
            }
        }
    }
    // Numeric IDs are layer-local. Break ties by side, input before output;
    // the union-find indices themselves never alias the two vertex namespaces.
    let mut minima = vec![(usize::MAX, usize::MAX); ni + no];
    for v in 0..ni + no {
        let key = if input_first || v < ni {
            (v, 0)
        } else {
            (v - ni, 1)
        };
        let r = root(&mut parent, v);
        minima[r] = minima[r].min(key);
    }
    let mut groups = BTreeMap::<(usize, usize), Vec<usize>>::new();
    for g in 0..no {
        let r = root(&mut parent, ni + g);
        groups.entry(minima[r]).or_default().push(g);
    }
    let mut output_rank = vec![usize::MAX; no];
    let largest_outputs = groups.values().map(Vec::len).max().unwrap_or(0);
    for (rank, outputs) in groups.values().enumerate() {
        for &g in outputs {
            output_rank[g] = rank;
        }
    }
    let mut term_counts = vec![0; groups.len()];
    for t in ts {
        term_counts[output_rank[t[0] as usize]] += 1;
    }
    Partition {
        output_rank,
        components: groups.len(),
        largest_outputs,
        largest_terms: term_counts.into_iter().max().unwrap_or(0),
    }
}

pub(super) fn analyze<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    field_id: FieldID,
) {
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let original = writer.to_bytes_lfc1(c);
    let ts = terms(c);
    let graph = graph(f, c, &ts);
    // graph() evaluates constant-only wires, so this includes every copy of 1,
    // not just wire number zero. Other constant values remain ordinary vertices.
    let one_tag = graph.constants[0];
    assert!(one_tag.is_some());
    let ones: Vec<Vec<bool>> = graph
        .counts
        .iter()
        .enumerate()
        .map(|(d, &n)| {
            graph.constants[graph.offsets[d]..graph.offsets[d] + n]
                .iter()
                .map(|&k| k == one_tag)
                .collect()
        })
        .collect();
    let ks: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let pack_outputs = std::env::var_os("BIPARTITE_PACK_OUTPUTS").is_some();
    let stats_only = std::env::var_os("BIPARTITE_STATS_ONLY").is_some();
    let input_first = std::env::var_os("BIPARTITE_INPUT_FIRST").is_some();
    println!("BIPARTITE_KEY input_first={input_first} pack_outputs={pack_outputs}");
    if stats_only {
        layer_stats("original", &compile_compiler::segment_circuit(f, c));
    }
    for include_one in [true, false] {
        let mode = if include_one {
            "with_one"
        } else {
            "without_one"
        };
        let mut working = ts.clone();
        let mut maps: Vec<Vec<u32>> = graph
            .counts
            .iter()
            .map(|&n| (0..n as u32).collect())
            .collect();
        let nlayers = working.len();
        let partitions: Vec<_> = working.iter_mut().enumerate().map(|(d, layer)| {
            let mut input_one = vec![false; graph.counts[d]];
            for (old, &new) in maps[d].iter().enumerate() { input_one[new as usize] = ones[d][old]; }
            for t in layer.iter_mut() {
                let a = maps[d][t[1] as usize];
                let b = maps[d][t[2] as usize];
                t[1] = a.min(b);
                t[2] = a.max(b);
            }
            let mut p = partition_with_order(layer, graph.counts[d], graph.counts[d + 1], &input_one, &ones[d + 1], include_one, input_first);
            // Preserve external output order. All other outputs are densely
            // packed once; the next layer consumes precisely this numbering.
            if pack_outputs && d + 1 < nlayers {
                let mut outputs: Vec<_> = (0..graph.counts[d+1]).collect();
                outputs.sort_unstable_by_key(|&g| (p.output_rank[g],g));
                let mut new_rank = vec![0; outputs.len()];
                for (new, &old) in outputs.iter().enumerate() {
                    maps[d+1][old] = new as u32;
                    new_rank[new] = p.output_rank[old];
                }
                p.output_rank = new_rank;
                for t in layer.iter_mut() { t[0] = maps[d+1][t[0] as usize]; }
            }
            println!("BIPARTITE_LAYER {mode} depth={} components={} largest_outputs={} total_outputs={} largest_terms={} total_terms={} input_ones={} output_ones={}",
                d + 1, p.components, p.largest_outputs, graph.counts[d+1], p.largest_terms, layer.len(), ones[d].iter().filter(|&&x| x).count(), ones[d+1].iter().filter(|&&x| x).count());
            p
        }).collect();
        let inverse: Vec<Vec<u32>> = maps
            .iter()
            .map(|map| {
                let mut inverse = vec![u32::MAX; map.len()];
                for (old, &new) in map.iter().enumerate() {
                    assert_eq!(inverse[new as usize], u32::MAX);
                    inverse[new as usize] = old as u32;
                }
                assert!(inverse.iter().all(|&x| x != u32::MAX));
                inverse
            })
            .collect();
        assert!(maps[0].iter().enumerate().all(|(i, &x)| i == x as usize));
        assert!(maps
            .last()
            .unwrap()
            .iter()
            .enumerate()
            .all(|(i, &x)| i == x as usize));
        let orders: &[&str] = if pack_outputs {
            &["global_morton", "morton"]
        } else {
            &["morton", "h1_h0_g", "h0_h1_g"]
        };
        for &order in orders {
            if (stats_only || input_first) && order != "morton" {
                continue;
            }
            let prefix = if pack_outputs { "packed_" } else { "" };
            let key_prefix = if input_first { "input_first_" } else { "" };
            let label = format!("{key_prefix}{prefix}{mode}_{order}");
            let mut reordered_terms = working.clone();
            for (layer, p) in reordered_terms.iter_mut().zip(&partitions) {
                layer.sort_unstable_by(|a, b| {
                    (if order == "global_morton" {
                        std::cmp::Ordering::Equal
                    } else {
                        p.output_rank[a[0] as usize].cmp(&p.output_rank[b[0] as usize])
                    })
                    .then_with(|| {
                        match order {
                            "morton" | "global_morton" => cmp_coordinates(a, b),
                            "h1_h0_g" => (a[2], a[1], a[0]).cmp(&(b[2], b[1], b[0])),
                            "h0_h1_g" => (a[1], a[2], a[0]).cmp(&(b[1], b[2], b[0])),
                            _ => unreachable!(),
                        }
                        .then_with(|| ks[a[3] as usize].cmp(&ks[b[3] as usize]))
                    })
                });
            }
            if stats_only {
                for (d, (layer, p)) in reordered_terms.iter().zip(&partitions).enumerate() {
                    let old: HashSet<_> = super::deltas(&ts[d]).into_iter().collect();
                    let ds = super::deltas(layer);
                    let mut inner = HashSet::new();
                    let mut boundary = HashSet::new();
                    let mut previous = None;
                    let mut transitions = 0;
                    for (t, delta) in layer.iter().zip(ds) {
                        let group = p.output_rank[t[0] as usize];
                        if previous == Some(group) {
                            inner.insert(delta);
                        } else {
                            boundary.insert(delta);
                            transitions += 1;
                        }
                        previous = Some(group);
                    }
                    println!(
                        "BIPARTITE_TRANSITIONS {label} depth={} starts={} inner_distinct={} boundary_distinct={} new_inner={} new_boundary_only={}",
                        d + 1,
                        transitions,
                        inner.len(),
                        boundary.len(),
                        inner.difference(&old).count(),
                        boundary
                            .iter()
                            .filter(|x| !inner.contains(*x) && !old.contains(*x))
                            .count()
                    );
                }
            }
            let reordered = rebuild(f, c, reordered_terms);
            let mut restored = terms(&reordered);
            for (d, layer) in restored.iter_mut().enumerate() {
                for t in layer.iter_mut() {
                    t[0] = inverse[d + 1][t[0] as usize];
                    let a = inverse[d][t[1] as usize];
                    let b = inverse[d][t[2] as usize];
                    t[1] = a.min(b);
                    t[2] = a.max(b);
                }
                layer.sort_unstable_by(|a, b| {
                    cmp_coordinates(a, b).then_with(|| ks[a[3] as usize].cmp(&ks[b[3] as usize]))
                });
            }
            assert_eq!(writer.to_bytes_lfc1(&rebuild(f, c, restored)), original);
            let mut unique = HashSet::new();
            for layer in &reordered.raw.layers {
                layer.for_each_delta(|&d| {
                    unique.insert(d);
                });
            }
            println!(
                "BIPARTITE_CORRECTNESS {label}: canonical_lfc1_exact=true global_deltas={} id={:02x?}",
                unique.len(),
                reordered.id
            );
            if stats_only {
                layer_stats(&label, &compile_compiler::segment_circuit(f, &reordered));
                continue;
            }
            super::sizes(&format!("{label}_lfc1"), &writer.to_bytes_lfc1(&reordered));
            let start = Instant::now();
            let segmented = compile_compiler::segment_circuit(f, &reordered);
            println!(
                "BIPARTITE_SEGMENT {label}: ms={:.3}",
                start.elapsed().as_secs_f64() * 1000.0
            );
            let bytes = writer.to_bytes_lfc2(&segmented);
            super::sizes(&format!("{label}_lfc2_segmented"), &bytes);
            super::wire_order::memory(&label, &segmented);
            let packed = zstd::bulk::compress(&bytes, 16).unwrap();
            let expected = writer.to_bytes_lfc1(&reordered);
            let mut times = Vec::new();
            for _ in 0..3 {
                let start = Instant::now();
                let unpacked = zstd::bulk::decompress(&packed, bytes.len()).unwrap();
                let (decoded, tail) = core_proto::reader::CircuitReader::new(f, field_id)
                    .from_bytes_lfc2(&unpacked, true)
                    .unwrap();
                times.push(start.elapsed().as_secs_f64() * 1000.0);
                assert!(tail.is_empty());
                assert_eq!(writer.to_bytes_lfc1(&decoded), expected);
            }
            times.sort_by(f64::total_cmp);
            println!(
                "BIPARTITE_DECODE {label}: zstd16_decode_and_id_median_ms={:.3} exact=true",
                times[1]
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn partition(
        ts: &[T],
        ni: usize,
        no: usize,
        input_one: &[bool],
        output_one: &[bool],
        include_one: bool,
    ) -> Partition {
        partition_with_order(ts, ni, no, input_one, output_one, include_one, false)
    }
    #[test]
    fn globally_distinct_ids_order_by_input_minimum() {
        let ts = [[0, 2, 2, 0], [1, 0, 0, 0], [2, 1, 1, 0]];
        let p = partition_with_order(&ts, 3, 3, &[false; 3], &[false; 3], true, true);
        assert_eq!(p.components, 3);
        assert_eq!(p.output_rank, [2, 0, 1]);
    }
    #[test]
    fn shared_one_merges_only_when_included() {
        let ts = [[0, 0, 1, 0], [1, 0, 2, 0]];
        let one = [true, false, false];
        assert_eq!(partition(&ts, 3, 2, &one, &[false; 2], true).components, 1);
        let p = partition(&ts, 3, 2, &one, &[false; 2], false);
        assert_eq!(p.components, 2);
        assert_eq!(p.output_rank, [0, 1]);
    }
    #[test]
    fn shared_ordinary_input_merges_even_when_one_is_excluded() {
        let ts = [[0, 1, 2, 0], [1, 2, 3, 0]];
        assert_eq!(
            partition(&ts, 4, 2, &[true, false, false, false], &[false; 2], false).components,
            1
        );
    }
    #[test]
    fn vertex_namespaces_are_distinct_and_minimum_uses_both_sides() {
        let ts = [[0, 2, 2, 0], [1, 0, 0, 0], [2, 1, 1, 0]];
        let p = partition(&ts, 3, 3, &[false; 3], &[false; 3], true);
        assert_eq!(p.components, 3);
        assert_eq!(p.output_rank, [1, 0, 2]);
    }
    #[test]
    fn a_nonzero_wire_id_copy_of_one_is_excluded() {
        let ts = [[0, 2, 3, 0], [1, 2, 4, 0]];
        assert_eq!(
            partition(
                &ts,
                5,
                2,
                &[true, false, true, false, false],
                &[false; 2],
                false
            )
            .components,
            2
        );
    }
}
