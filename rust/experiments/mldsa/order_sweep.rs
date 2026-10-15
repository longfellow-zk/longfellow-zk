//! Broad offline ordering search. No per-circuit policy selection in production.
use super::{cmp_coordinates, graph, rebuild, terms, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{circuit::Circuit, FieldID};
use std::{
    collections::{HashMap, HashSet},
    time::Instant,
};

#[path = "layer_wires.rs"]
pub(super) mod layer_wires;

#[path = "segment_window.rs"]
pub(super) mod segment_window;

#[derive(Clone, Debug)]
enum Order {
    Lex([usize; 4], u32),
    Morton(Vec<usize>, usize, bool, bool), // axes low to high, block bits, k first, reverse
    Hilbert([usize; 3]),
    Gap([usize; 3]),
    Relative([usize; 3]),
}
impl Order {
    fn name(&self) -> String {
        let axes = |p: &[usize]| p.iter().map(usize::to_string).collect::<String>();
        match self {
            Self::Lex(p, mask) => format!("lex{}_r{mask}", axes(p)),
            Self::Morton(p, b, k, r) => format!(
                "m{}_b{b}_k{}_r{}",
                axes(p),
                usize::from(*k),
                usize::from(*r)
            ),
            Self::Hilbert(p) => format!("hilbert{}", axes(p)),
            Self::Gap(p) => format!("gap{}", axes(p)),
            Self::Relative(p) => format!("relative{}", axes(p)),
        }
    }
    fn spatial(&self) -> bool {
        matches!(self, Self::Morton(..) | Self::Hilbert(..))
    }
    fn key(&self, t: T) -> [u32; 4] {
        match self {
            Self::Lex(p, mask) => p.map(|i| if mask & (1 << i) != 0 { !t[i] } else { t[i] }),
            Self::Gap(p) => {
                let v = [t[0], t[1], t[2] - t[1]];
                [v[p[0]], v[p[1]], v[p[2]], t[3]]
            }
            Self::Relative(p) => {
                let v = [
                    t[0],
                    t[1].wrapping_sub(t[0]) ^ 0x80000000,
                    t[2].wrapping_sub(t[0]) ^ 0x80000000,
                ];
                [v[p[0]], v[p[1]], v[p[2]], t[3]]
            }
            Self::Hilbert(p) => {
                let h = hilbert(t[p[0]], t[p[1]]);
                [(h >> 32) as u32, h as u32, t[p[2]], t[3]]
            }
            Self::Morton(p, b, k_first, reverse) => {
                let v = [t[p[0]], t[p[1]], if p.len() == 3 { t[p[2]] } else { 0 }];
                let m = interleave(&v[..p.len()], *b);
                let mut key = if p.len() == 3 {
                    [(m >> 64) as u32, (m >> 32) as u32, m as u32, t[3]]
                } else {
                    let third = 3 - p[0] - p[1];
                    [(m >> 32) as u32, m as u32, t[third], t[3]]
                };
                if *reverse {
                    for x in &mut key[..3] {
                        *x = !*x;
                    }
                }
                if *k_first {
                    key.rotate_right(1);
                }
                key
            }
        }
    }
}

fn interleave(v: &[u32], block: usize) -> u128 {
    const fn table(dim: usize) -> [u32; 256] {
        let mut result = [0; 256];
        let mut x = 0;
        while x < 256 {
            let mut bit = 0;
            while bit < 8 {
                result[x] |= (((x >> bit) & 1) as u32) << (dim * bit);
                bit += 1;
            }
            x += 1;
        }
        result
    }
    const TWO: [u32; 256] = table(2);
    const THREE: [u32; 256] = table(3);
    let mut result = 0u128;
    if block == 1 {
        let table = if v.len() == 2 { &TWO } else { &THREE };
        for chunk in 0..4 {
            for (axis, &x) in v.iter().enumerate() {
                result |= (table[((x >> (8 * chunk)) & 255) as usize] as u128)
                    << (8 * chunk * v.len() + axis);
            }
        }
        return result;
    }
    let mut out = 0;
    for bit in (0..32).step_by(block) {
        let width = block.min(32 - bit);
        let mask = (1u64 << width) - 1;
        for &x in v {
            result |= (((u64::from(x) >> bit) & mask) as u128) << out;
            out += width;
        }
    }
    result
}

fn hilbert(mut x: u32, mut y: u32) -> u64 {
    let mut d = 0u64;
    for bit in (0..32).rev() {
        let rx = (x >> bit) & 1;
        let ry = (y >> bit) & 1;
        d |= u64::from((3 * rx) ^ ry) << (2 * bit);
        if ry == 0 {
            if rx == 1 {
                x = !x;
                y = !y;
            }
            std::mem::swap(&mut x, &mut y);
        }
    }
    d
}

fn permutations3() -> Vec<[usize; 3]> {
    let mut ps = Vec::new();
    for a in 0..3 {
        for b in 0..3 {
            for c in 0..3 {
                if a != b && b != c && a != c {
                    ps.push([a, b, c]);
                }
            }
        }
    }
    ps
}
fn catalog(extended: bool) -> Vec<Order> {
    let mut out = Vec::new();
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for d in 0..4 {
                    let p = [a, b, c, d];
                    if (0..4).all(|i| (i + 1..4).all(|j| p[i] != p[j])) {
                        out.push(Order::Lex(p, 0));
                        if extended {
                            for mask in 1..8 {
                                out.push(Order::Lex(p, mask));
                            }
                        }
                    }
                }
            }
        }
    }
    for p in permutations3() {
        out.push(Order::Morton(p[..2].to_vec(), 1, false, false));
        out.push(Order::Morton(p.to_vec(), 1, false, false));
        out.push(Order::Hilbert(p));
        out.push(Order::Gap(p));
        out.push(Order::Relative(p));
        if extended {
            for block in [2, 3, 4, 6, 8, 12] {
                out.push(Order::Morton(p[..2].to_vec(), block, false, false));
                out.push(Order::Morton(p.to_vec(), block, false, false));
            }
            for axes in [p[..2].to_vec(), p.to_vec()] {
                out.push(Order::Morton(axes.clone(), 1, true, false));
                out.push(Order::Morton(axes, 1, false, true));
            }
        }
    }
    out
}

fn coordinates(ts: &[T], groups: &[u32], norm: &str) -> Vec<T> {
    if norm == "abs" {
        return ts.to_vec();
    }
    if norm == "offset" {
        let mut minima = HashMap::<u32, [u32; 2]>::new();
        for (t, &g) in ts.iter().zip(groups) {
            let m = minima.entry(g).or_insert([u32::MAX; 2]);
            m[0] = m[0].min(t[0]);
            m[1] = m[1].min(t[1]).min(t[2]);
        }
        return ts
            .iter()
            .zip(groups)
            .map(|(t, g)| {
                let m = minima[g];
                [t[0] - m[0], t[1] - m[1], t[2] - m[1], t[3]]
            })
            .collect();
    }
    assert_eq!(norm, "rank");
    let mut inputs: Vec<_> = ts
        .iter()
        .zip(groups)
        .flat_map(|(t, &g)| [(g, t[1]), (g, t[2])])
        .collect();
    let mut outputs: Vec<_> = ts.iter().zip(groups).map(|(t, &g)| (g, t[0])).collect();
    let rank_map = |keys: &mut Vec<(u32, u32)>| {
        keys.sort_unstable();
        keys.dedup();
        let mut last = None;
        let mut next = 0;
        let mut map = HashMap::with_capacity(keys.len());
        for &(g, h) in keys.iter() {
            if last != Some(g) {
                next = 0;
                last = Some(g);
            }
            map.insert((g, h), next);
            next += 1;
        }
        map
    };
    let ir = rank_map(&mut inputs);
    let gr = rank_map(&mut outputs);
    ts.iter()
        .zip(groups)
        .map(|(t, &g)| [gr[&(g, t[0])], ir[&(g, t[1])], ir[&(g, t[2])], t[3]])
        .collect()
}

fn selected(label: &str, filter: &Option<String>) -> bool {
    filter
        .as_ref()
        .is_none_or(|s| s.split(',').any(|p| label == p))
}

/// The shared type-major/output-major policy measured as kind_abs_lex0213_r5.
/// Only term order changes; all wire labels and the term multiset remain fixed.
pub(super) fn kind_order<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
) -> Circuit<F> {
    let original = terms(c);
    let graph = graph(f, c, &original);
    let coeffs: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut layers = original.clone();
    for (d, l) in layers.iter_mut().enumerate() {
        let kind = |t: &T| {
            let a = graph.constants[graph.offsets[d] + t[1] as usize] == graph.constants[0];
            let b = graph.constants[graph.offsets[d] + t[2] as usize] == graph.constants[0];
            if a && b {
                0
            } else if a || b {
                1
            } else if t[1] == t[2] {
                2
            } else {
                3
            }
        };
        l.sort_unstable_by(|a, b| {
            kind(a)
                .cmp(&kind(b))
                .then(b[0].cmp(&a[0]))
                .then(b[2].cmp(&a[2]))
                .then(a[1].cmp(&b[1]))
                .then_with(|| coeffs[a[3] as usize].cmp(&coeffs[b[3] as usize]))
        });
        let mut restored = l.clone();
        restored.sort_unstable_by(|a, b| {
            cmp_coordinates(a, b).then_with(|| coeffs[a[3] as usize].cmp(&coeffs[b[3] as usize]))
        });
        assert_eq!(restored, original[d]);
    }
    rebuild(f, c, layers)
}

pub(super) fn analyze<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    field_id: FieldID,
) {
    if let Ok(policies) = std::env::var("SWEEP_WIRE_BATCH") {
        assert!(std::env::var_os("SWEEP_WIRE_ONLY").is_some());
        for policy in policies.split(',') {
            run(f, c, field_id, Some(policy.to_string()));
        }
    } else {
        run(f, c, field_id, std::env::var("SWEEP_WIRES").ok());
    }
}

fn run<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    field_id: FieldID,
    wire_policy: Option<String>,
) {
    let start = Instant::now();
    let wire_only = std::env::var_os("SWEEP_WIRE_ONLY").is_some();
    if wire_only {
        for forbidden in [
            "SWEEP_WINDOWS",
            "SWEEP_KIND_PARTITIONS",
            "SWEEP_EXTENDED",
            "SWEEP_SKIP_CORE",
            "SWEEP_CONTEXTS",
            "SWEEP_ORDERS",
            "SWEEP_NORMS",
            "SWEEP_SELECT",
        ] {
            assert!(
                std::env::var_os(forbidden).is_none(),
                "{forbidden} is incompatible with wire-only experiments"
            );
        }
    }
    let rewired = wire_policy.as_ref().map(|p| layer_wires::reorder(f, c, p));
    let c = rewired.as_ref().unwrap_or(c);
    let mut ts = terms(c);
    // Current compiler traversal is no longer Morton. Canonicalize a reference
    // multiset explicitly; correctness checks must not assume stored order.
    for l in &mut ts {
        l.sort_unstable_by(|a, b| {
            cmp_coordinates(a, b).then_with(|| {
                f.to_bytes(&c.raw.constants[a[3] as usize])
                    .cmp(&f.to_bytes(&c.raw.constants[b[3] as usize]))
            })
        });
    }
    let graph = graph(f, c, &ts);
    let ones: Vec<Vec<bool>> = graph
        .counts
        .iter()
        .enumerate()
        .map(|(d, &n)| {
            graph.constants[graph.offsets[d]..graph.offsets[d] + n]
                .iter()
                .map(|&k| k == graph.constants[0])
                .collect()
        })
        .collect();
    let coeffs: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut coeff_order: Vec<_> = (0..coeffs.len()).collect();
    coeff_order.sort_by_key(|&i| &coeffs[i]);
    let mut coeff_rank = vec![0; coeffs.len()];
    for (r, &old) in coeff_order.iter().enumerate() {
        coeff_rank[old] = r as u32;
    }
    // Key generation uses semantic coefficient-byte order; actual terms keep
    // their original constant indices throughout the circuit transformation.
    let keyed: Vec<Vec<T>> = ts
        .iter()
        .map(|l| {
            l.iter()
                .map(|&t| [t[0], t[1], t[2], coeff_rank[t[3] as usize]])
                .collect()
        })
        .collect();
    let term_arities: Vec<Vec<u32>> = ts
        .iter()
        .enumerate()
        .map(|(d, l)| {
            let kind = |t: &T| match (ones[d][t[1] as usize], ones[d][t[2] as usize]) {
                (true, true) => 0,
                (true, false) | (false, true) => 1,
                _ if t[1] == t[2] => 2,
                _ => 3,
            };
            let mut counts = vec![[0u32; 4]; graph.counts[d + 1]];
            for t in l {
                counts[t[0] as usize][kind(t)] += 1;
            }
            l.iter().map(|t| counts[t[0] as usize][kind(t)]).collect()
        })
        .collect();
    let final_mode = std::env::var_os("SWEEP_FINAL").is_some();
    let extended = std::env::var_os("SWEEP_EXTENDED").is_some();
    let filter = std::env::var("SWEEP_SELECT").ok();
    let mut contexts =
        std::env::var("SWEEP_CONTEXTS").unwrap_or_else(|_| "global,bip1,bip0,whole,kind".into());
    if std::env::var_os("SWEEP_KIND_PARTITIONS").is_some() {
        contexts = (0..256)
            .filter_map(|code| {
                let p = [code % 4, (code / 4) % 4, (code / 16) % 4, code / 64];
                let n = 1 + p.iter().max().unwrap();
                (0..n)
                    .all(|i| p.contains(&i))
                    .then(|| format!("kind{}{}{}{}", p[0], p[1], p[2], p[3]))
            })
            .collect::<Vec<_>>()
            .join(",");
    }
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let mut global_alternatives = HashMap::new();
    for policy in ["whole_one", "whole_nonzero", "whole_one_nonzero"] {
        if !contexts
            .split(',')
            .any(|ctx| ctx.trim_start_matches("kind_").trim_end_matches("_kind") == policy)
        {
            continue;
        }
        let mut parent: Vec<_> = (0..*graph.offsets.last().unwrap()).collect();
        let participates = |i: usize| {
            if policy.contains("_one") {
                graph.constants[i] != graph.constants[0]
            } else {
                graph.constants[i].is_none()
            }
        };
        for (d, l) in ts.iter().enumerate().skip(1) {
            for t in l {
                if policy.contains("nonzero") && f.is_zero(&c.raw.constants[t[3] as usize]) {
                    continue;
                }
                let g = graph.offsets[d + 1] + t[0] as usize;
                if participates(g) {
                    for h in [t[1], t[2]] {
                        let h = graph.offsets[d] + h as usize;
                        if participates(h) {
                            super::union(&mut parent, g, h);
                        }
                    }
                }
            }
        }
        let roots: Vec<_> = (0..parent.len())
            .map(|i| super::root(&mut parent, i))
            .collect();
        global_alternatives.insert(policy, roots);
    }
    let mut seen = HashMap::new();
    let mut orders = catalog(extended);
    if let Ok(filter) = std::env::var("SWEEP_ORDERS") {
        orders.retain(|o| filter.split(',').any(|s| s == o.name()));
    }
    if std::env::var_os("SWEEP_SKIP_CORE").is_some() {
        let core: HashSet<_> = catalog(false).iter().map(Order::name).collect();
        orders.retain(|o| !core.contains(&o.name()));
    }
    if wire_only {
        contexts = "global".into();
        orders = vec![Order::Morton(vec![1, 2], 1, false, false)];
    }
    let norm_filter = std::env::var("SWEEP_NORMS").ok();
    let mut tested = 0;
    println!(
        "SWEEP_CONFIG orders={} extended={extended} final={final_mode} contexts={contexts} coordinate_names=0:g,1:h0,2:h1,3:coefficient_byte_rank",
        orders.len()
    );
    for context in contexts.split(',') {
        let groups: Vec<Vec<u32>> = ts
            .iter()
            .enumerate()
            .map(|(d, l)| match context {
                "global" => vec![0; l.len()],
                "kind_whole"
                | "whole_kind"
                | "kind_bip0"
                | "bip0_kind"
                | "kind_bip1"
                | "bip1_kind"
                | "kind_bipshape0"
                | "kind_bipshape1"
                | "kind_whole_one"
                | "whole_one_kind"
                | "kind_whole_nonzero"
                | "whole_nonzero_kind"
                | "kind_whole_one_nonzero"
                | "whole_one_nonzero_kind" => {
                    let kind = |t: &T| match (ones[d][t[1] as usize], ones[d][t[2] as usize]) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        _ if t[1] == t[2] => 2,
                        _ => 3,
                    };
                    let ranks = if context.contains("whole") {
                        let policy = context
                            .trim_start_matches("kind_")
                            .trim_end_matches("_kind");
                        let components =
                            global_alternatives.get(policy).unwrap_or(&graph.components);
                        vec![l
                            .iter()
                            .map(|t| components[graph.offsets[d + 1] + t[0] as usize] as u32)
                            .collect::<Vec<_>>()]
                    } else {
                        let include_one = context.contains('1');
                        let primary = vec![true; graph.counts[d]];
                        let input_one = if d == 0 && !include_one {
                            &primary
                        } else {
                            &ones[d]
                        };
                        let separate = context.contains("bipshape");
                        (0..if separate { 4 } else { 1 })
                            .map(|k| {
                                let subset: Vec<_> = l
                                    .iter()
                                    .copied()
                                    .filter(|t| !separate || kind(t) == k)
                                    .collect();
                                let p = super::bipartite::partition_with_order(
                                    &subset,
                                    graph.counts[d],
                                    graph.counts[d + 1],
                                    input_one,
                                    &ones[d + 1],
                                    include_one,
                                    std::env::var_os("SWEEP_COMPONENT_NUMERIC_MIN").is_none(),
                                );
                                l.iter()
                                    .map(|t| p.output_rank[t[0] as usize] as u32)
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>()
                    };
                    let stride = ranks.iter().flatten().max().copied().unwrap_or(0) + 1;
                    l.iter()
                        .enumerate()
                        .map(|(i, t)| {
                            let k = kind(t);
                            let r = ranks[if ranks.len() == 4 { k as usize } else { 0 }][i];
                            if context.starts_with("kind_") {
                                k * stride + r
                            } else {
                                4 * r + k
                            }
                        })
                        .collect()
                }
                ctx if ctx.starts_with("hybrid") => l
                    .iter()
                    .zip(&term_arities[d])
                    .map(|(t, &arity)| {
                        let kind = match (ones[d][t[1] as usize], ones[d][t[2] as usize]) {
                            (true, true) => 0,
                            (true, false) | (false, true) => 1,
                            _ if t[1] == t[2] => 2,
                            _ => 3,
                        };
                        match ctx {
                            "hybrid" => kind * 2 + u32::from(arity > 1),
                            "hybrid_arity" => kind * (l.len() as u32 + 1) + arity,
                            "hybrid_coefficient" => {
                                kind * (coeffs.len() as u32 + 1)
                                    + if arity == 1 {
                                        coeff_rank[t[3] as usize]
                                    } else {
                                        coeffs.len() as u32
                                    }
                            }
                            "hybrid_coeffclass" => {
                                let k = &c.raw.constants[t[3] as usize];
                                let class = if arity > 1 {
                                    4
                                } else if f.is_zero(k) {
                                    0
                                } else if *k == f.one() {
                                    1
                                } else if *k == f.mone() {
                                    2
                                } else {
                                    3
                                };
                                5 * kind + class
                            }
                            _ => panic!("unknown hybrid {ctx}"),
                        }
                    })
                    .collect(),
                "whole" => l
                    .iter()
                    .map(|t| graph.components[graph.offsets[d + 1] + t[0] as usize] as u32)
                    .collect(),
                "bip1" | "bip0" => {
                    let primary = vec![true; graph.counts[d]];
                    let p = super::bipartite::partition_with_order(
                        l,
                        graph.counts[d],
                        graph.counts[d + 1],
                        if d == 0 && context == "bip0" {
                            &primary
                        } else {
                            &ones[d]
                        },
                        &ones[d + 1],
                        context == "bip1",
                        std::env::var_os("SWEEP_COMPONENT_NUMERIC_MIN").is_none(),
                    );
                    l.iter()
                        .map(|t| p.output_rank[t[0] as usize] as u32)
                        .collect()
                }
                "slot" | "kind_slot" | "coefficient" | "kind_coefficient" => {
                    let kind = |t: &T| match (ones[d][t[1] as usize], ones[d][t[2] as usize]) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        (false, false) if t[1] == t[2] => 2,
                        _ => 3,
                    };
                    let with_kind = context.starts_with("kind_");
                    let mut index: Vec<usize> = (0..l.len()).collect();
                    index.sort_unstable_by_key(|&i| {
                        let t = l[i];
                        (
                            t[0],
                            if with_kind { kind(&t) } else { 0 },
                            t[2],
                            t[1],
                            coeff_rank[t[3] as usize],
                        )
                    });
                    let mut groups = vec![0; l.len()];
                    let mut previous = None;
                    let mut slot = 0;
                    // Rank terms within each output and shape, then transpose:
                    // first terms of all gates, second terms of all gates, etc.
                    for i in index {
                        let t = l[i];
                        let k = if with_kind { kind(&t) } else { 0 };
                        let gate = (t[0], k);
                        if previous != Some(gate) {
                            slot = 0;
                        }
                        previous = Some(gate);
                        groups[i] = if context.ends_with("coefficient") {
                            k * coeffs.len() as u32 + coeff_rank[t[3] as usize]
                        } else {
                            k * (l.len() as u32 + 1) + slot
                        };
                        slot += 1;
                    }
                    groups
                }
                "stencil" | "kind_stencil" | "kind_wiring" | "kind_arity" => {
                    // Group exact translated gate shapes, not merely equal wire
                    // counts. Constants are external ports, never part of a base.
                    let with_kind = context.starts_with("kind_");
                    let kind = |t: &T| match (ones[d][t[1] as usize], ones[d][t[2] as usize]) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        (false, false) if t[1] == t[2] => 2,
                        _ => 3,
                    };
                    let mut gates = std::collections::BTreeMap::<(u32, u32), Vec<usize>>::new();
                    for (i, t) in l.iter().enumerate() {
                        gates
                            .entry((t[0], if with_kind { kind(t) } else { 0 }))
                            .or_default()
                            .push(i);
                    }
                    let mut signatures =
                        std::collections::BTreeMap::<(u32, Vec<T>), Vec<usize>>::new();
                    for ((_, k), indices) in gates {
                        let base = indices
                            .iter()
                            .flat_map(|&i| [l[i][1], l[i][2]])
                            .filter(|&h| !ones[d][h as usize])
                            .min()
                            .unwrap_or(0);
                        let mut signature: Vec<T> = if context == "kind_arity" {
                            vec![[indices.len() as u32, 0, 0, 0]]
                        } else {
                            indices
                                .iter()
                                .map(|&i| {
                                    let t = l[i];
                                    let local = |h: u32| {
                                        if ones[d][h as usize] {
                                            u32::MAX
                                        } else {
                                            h - base
                                        }
                                    };
                                    [
                                        kind(&t),
                                        local(t[1]),
                                        local(t[2]),
                                        if context == "kind_wiring" {
                                            0
                                        } else {
                                            coeff_rank[t[3] as usize]
                                        },
                                    ]
                                })
                                .collect()
                        };
                        signature.sort_unstable();
                        signatures
                            .entry((k, signature))
                            .or_default()
                            .extend(indices);
                    }
                    let mut groups = vec![0; l.len()];
                    for (rank, indices) in signatures.into_values().enumerate() {
                        for i in indices {
                            groups[i] = rank as u32;
                        }
                    }
                    groups
                }
                "role" | "kind_coeffclass" | "role_coeffclass" => l
                    .iter()
                    .map(|t| {
                        let a = ones[d][t[1] as usize];
                        let b = ones[d][t[2] as usize];
                        let kind = if context.starts_with("role") {
                            match (a, b) {
                                (true, true) => 0,
                                (true, false) => 1,
                                (false, true) => 2,
                                _ if t[1] == t[2] => 3,
                                _ => 4,
                            }
                        } else {
                            match (a, b) {
                                (true, true) => 0,
                                (true, false) | (false, true) => 1,
                                _ if t[1] == t[2] => 2,
                                _ => 3,
                            }
                        };
                        if context.ends_with("coeffclass") {
                            let k = &c.raw.constants[t[3] as usize];
                            let class = if f.is_zero(k) {
                                0
                            } else if *k == f.one() {
                                1
                            } else if *k == f.mone() {
                                2
                            } else {
                                3
                            };
                            4 * kind + class
                        } else {
                            kind
                        }
                    })
                    .collect(),
                ctx if ctx.starts_with("kind") => l
                    .iter()
                    .map(|t| {
                        let a = ones[d][t[1] as usize];
                        let b = ones[d][t[2] as usize];
                        let kind = if a && b {
                            0
                        } else if a || b {
                            1
                        } else if t[1] == t[2] {
                            2
                        } else {
                            3
                        };
                        if ctx == "kind" {
                            kind
                        } else if ctx == "kind_assert" {
                            kind + 4 * u32::from(f.is_zero(&c.raw.constants[t[3] as usize]))
                        } else {
                            assert_eq!(ctx.len(), 8, "kind pattern needs four digits");
                            u32::from(ctx.as_bytes()[4 + kind as usize] - b'0')
                        }
                    })
                    .collect(),
                _ => panic!("Unknown context {context}"),
            })
            .collect();
        let component_context = context.contains("whole") || context.contains("bip");
        let norms: &[&str] = if !component_context
            && (context.starts_with("hybrid")
                || context.starts_with("role")
                || context == "global"
                || context.starts_with("kind")
                || context == "slot"
                || context == "coefficient"
                || context == "stencil")
        {
            &["abs"]
        } else {
            &["abs", "offset", "rank"]
        };
        for &norm in norms {
            if norm_filter
                .as_ref()
                .is_some_and(|s| !s.split(',').any(|v| v == norm))
            {
                continue;
            }
            let normalized: Vec<Vec<T>> = keyed
                .iter()
                .zip(&groups)
                .map(|(l, g)| coordinates(l, g, norm))
                .collect();
            for order in &orders {
                // Monotone rank/offset transformations leave lex ordering unchanged.
                // Translation also leaves gap/relative lex ordering unchanged.
                if norm != "abs" && matches!(order, Order::Lex(..)) {
                    continue;
                }
                if norm == "offset" && !order.spatial() {
                    continue;
                }
                let base_label = format!(
                    "{context}_{norm}_{}{}",
                    order.name(),
                    if std::env::var_os("SWEEP_COMPONENT_NUMERIC_MIN").is_some() {
                        "__numeric_min"
                    } else {
                        ""
                    }
                );
                let label = wire_policy
                    .as_ref()
                    .map_or_else(|| base_label.clone(), |p| format!("wire_{p}__{base_label}"));
                if !selected(&label, &filter) && !selected(&base_label, &filter) {
                    continue;
                }
                let then = Instant::now();
                let mut layers = Vec::with_capacity(ts.len());
                for (d, ((l, n), g)) in ts.iter().zip(&normalized).zip(&groups).enumerate() {
                    let mut index: Vec<([u32; 5], u32)> = n
                        .iter()
                        .zip(g)
                        .enumerate()
                        .map(|(i, (&t, &group))| {
                            // Never split a multi-term shape's gate body to sort
                            // its coefficients independently. Only singleton
                            // shapes use the swept input/output priority.
                            let k = if context.starts_with("hybrid") && term_arities[d][i] > 1 {
                                Order::Lex([0, 2, 1, 3], 5).key(t)
                            } else {
                                order.key(t)
                            };
                            ([group, k[0], k[1], k[2], k[3]], i as u32)
                        })
                        .collect();
                    index.sort_unstable();
                    layers.push(index.into_iter().map(|(_, i)| l[i as usize]).collect());
                }
                // Sorting an index permutation preserves every original term exactly.
                let candidate = rebuild(f, c, layers);
                if wire_only {
                    assert_eq!(candidate.id, c.id, "Wire-only sweep changed term traversal");
                    assert_eq!(
                        terms(&candidate),
                        ts,
                        "Stored stream must already be global Morton"
                    );
                }
                if let Some(previous) = seen.insert(candidate.id, label.clone()) {
                    println!("SWEEP_DUP {label} identical_to={previous}");
                    continue;
                }
                if final_mode {
                    let mut restored = terms(&candidate);
                    for l in &mut restored {
                        l.sort_unstable_by(|a, b| {
                            cmp_coordinates(a, b)
                                .then_with(|| coeffs[a[3] as usize].cmp(&coeffs[b[3] as usize]))
                        });
                    }
                    assert_eq!(restored, ts);
                }
                let segmented = compile_compiler::segment_circuit(f, &candidate);
                let bytes = writer.to_bytes_lfc2(&segmented);
                let z3 = zstd::bulk::compress(&bytes, 3).unwrap().len();
                let z16 = zstd::bulk::compress(&bytes, 16).unwrap().len();
                let nd: usize = segmented.raw.layers.iter().map(|l| l.deltas().len()).sum();
                let ns: usize = segmented
                    .raw
                    .layers
                    .iter()
                    .map(|l| l.delta_segments().len())
                    .sum();
                let ne: usize = segmented
                    .raw
                    .layers
                    .iter()
                    .flat_map(|l| l.delta_segments())
                    .map(Vec::len)
                    .sum();
                let nt: usize = segmented
                    .raw
                    .layers
                    .iter()
                    .map(|l| l.delta_tokens().len())
                    .sum();
                let memory = 16 * nd + 24 * ns + 4 * (ne + nt);
                let mut unique = HashSet::new();
                for l in &candidate.raw.layers {
                    l.for_each_delta(|&d| {
                        unique.insert(d);
                    });
                }
                println!(
                    "SWEEP {label} raw={} zstd3={z3} zstd16={z16} global_deltas={} layer_deltas={nd} segments={ns} entries={ne} tokens={nt} memory={memory} ms={:.1}",
                    bytes.len(),
                    unique.len(),
                    then.elapsed().as_secs_f64() * 1000.0
                );
                if final_mode {
                    if let Ok(directory) = std::env::var("SWEEP_SAVE_DIR") {
                        let dataset = std::env::var("SWEEP_DATASET").unwrap();
                        std::fs::create_dir_all(&directory).unwrap();
                        std::fs::write(
                            std::path::Path::new(&directory)
                                .join(format!("{dataset}--{label}.lfc2")),
                            &bytes,
                        )
                        .unwrap();
                    }
                    super::sizes(&format!("{label}_lfc1"), &writer.to_bytes_lfc1(&candidate));
                    super::sizes(
                        &format!("{label}_lfc2_native"),
                        &writer.to_bytes_lfc2(&candidate),
                    );
                    super::sizes(&format!("{label}_lfc2"), &bytes);
                    let decode_start = Instant::now();
                    let (decoded, tail) = core_proto::reader::CircuitReader::new(f, field_id)
                        .from_bytes_lfc2(&bytes, true)
                        .unwrap();
                    let decode_ms = decode_start.elapsed().as_secs_f64() * 1000.0;
                    assert!(tail.is_empty());
                    assert_eq!(
                        writer.to_bytes_lfc1(&decoded),
                        writer.to_bytes_lfc1(&candidate)
                    );
                    println!(
                        "SWEEP_CHECK {label} exact_canonical_and_lfc2_roundtrip=true decode_with_id_ms={decode_ms:.3}"
                    );
                    if std::env::var_os("SWEEP_LAYER_STATS").is_some() {
                        super::bipartite::layer_stats(&label, &segmented);
                    }
                    if std::env::var_os("SWEEP_WINDOWS").is_some() {
                        for window in [8, 16, 24, 48, 64, 96, 128, 192, 256, 512] {
                            let segmented = segment_window::segment_circuit(f, &candidate, window);
                            let bytes = writer.to_bytes_lfc2(&segmented);
                            super::sizes(&format!("{label}_window{window}"), &bytes);
                            super::wire_order::memory(
                                &format!("{label}_window{window}"),
                                &segmented,
                            );
                            let (decoded, tail) =
                                core_proto::reader::CircuitReader::new(f, field_id)
                                    .from_bytes_lfc2(&bytes, true)
                                    .unwrap();
                            assert!(tail.is_empty());
                            assert_eq!(
                                writer.to_bytes_lfc1(&decoded),
                                writer.to_bytes_lfc1(&candidate)
                            );
                        }
                    }
                }
                tested += 1;
            }
        }
    }
    ts.clear();
    println!(
        "SWEEP_DONE unique_candidates={tested} seconds={:.3}",
        start.elapsed().as_secs_f64()
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn all_lexicographic_axis_permutations_are_present() {
        let o = catalog(false);
        assert_eq!(o.iter().filter(|o| matches!(o, Order::Lex(..))).count(), 24);
        let names: HashSet<_> = o.iter().map(Order::name).collect();
        assert_eq!(names.len(), o.len());
    }
    #[test]
    fn pair_interleave_matches_existing_morton() {
        for a in 0..8 {
            for b in 0..8 {
                for x in 0..8 {
                    for y in 0..8 {
                        assert_eq!(
                            interleave(&[a, b], 1).cmp(&interleave(&[x, y], 1)),
                            cmp_coordinates(&[0, a, b, 0], &[0, x, y, 0])
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn hilbert_small_grids_are_contiguous_paths() {
        for bits in 1..5 {
            let n = 1u32 << bits;
            let mut p: Vec<_> = (0..n)
                .flat_map(|x| (0..n).map(move |y| (hilbert(x, y), x, y)))
                .collect();
            p.sort_unstable();
            assert!(p
                .windows(2)
                .all(|v| v[1].0 == v[0].0 + 1
                    && v[1].1.abs_diff(v[0].1) + v[1].2.abs_diff(v[0].2) == 1));
        }
    }
    #[test]
    fn local_ranks_are_independent_of_absolute_holes() {
        let a = [[11, 2, 8, 0], [14, 8, 9, 1]];
        let b = [[21, 12, 80, 0], [40, 80, 95, 1]];
        assert_eq!(
            coordinates(&a, &[0, 0], "rank"),
            coordinates(&b, &[7, 7], "rank")
        );
    }
}
