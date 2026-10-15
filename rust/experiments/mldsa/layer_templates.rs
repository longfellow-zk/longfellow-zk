// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

//! Offline exact template discovery used only to order ordinary LFC2 terms.
use core_algebra::AlgebraicField;
use core_proto::{
    circuit::{Circuit, RawCircuit},
    Layer, SerializableField, TermDelta,
};
use std::collections::HashMap;

fn root(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

// Prove constants forwards, rather than guessing from a wire number. Assertion
// markers do not establish constants. In particular this catches copies of 1.
fn ones<F: SerializableField + AlgebraicField>(f: &F, c: &Circuit<F>) -> Vec<Vec<bool>> {
    let mut known = vec![None; c.raw.ninput];
    if !known.is_empty() {
        known[0] = Some(f.one());
    }
    let mut result = vec![Vec::new(); c.raw.layers.len() + 1];
    result[c.raw.layers.len()] = known.iter().map(|v| v.as_ref() == Some(&f.one())).collect();
    for d in (0..c.raw.layers.len()).rev() {
        let nv = if d == 0 {
            c.raw.noutput
        } else {
            c.raw.layers[d - 1].nw()
        };
        let mut values = vec![f.zero(); nv];
        let mut constant = vec![true; nv];
        for [g, a, b, k] in records(&c.raw.layers[d]) {
            if let (Some(a), Some(b)) = (&known[a as usize], &known[b as usize]) {
                if !f.is_zero(&c.raw.constants[k as usize]) {
                    f.add(
                        &mut values[g as usize],
                        &f.mulf(&c.raw.constants[k as usize], &f.mulf(a, b)),
                    );
                } else {
                    constant[g as usize] = false;
                }
            } else {
                constant[g as usize] = false;
            }
        }
        known = values
            .into_iter()
            .zip(constant)
            .map(|(v, yes)| yes.then_some(v))
            .collect();
        result[d] = known.iter().map(|v| v.as_ref() == Some(&f.one())).collect();
    }
    result
}

pub type Record = [u32; 4];

#[derive(Clone)]
pub(super) struct Group {
    pub program: Vec<Record>,
    pub ng: usize,
    pub maps: Vec<Vec<u32>>,
    pub affine: bool,
    pub canonical_h: bool,
}

impl Group {
    fn expand(&self, [g, a, b, k]: Record, map: &[u32]) -> Record {
        let (g, a, b) = if self.affine {
            let h = |v: u32, base: u32| if v == 0 { 0 } else { base + v - 1 };
            (map[0] + g, h(a, map[1]), h(b, map[2]))
        } else {
            (
                map[g as usize],
                map[self.ng + a as usize],
                map[self.ng + b as usize],
            )
        };
        let (a, b) = if self.canonical_h {
            (a.min(b), a.max(b))
        } else {
            (a, b)
        };
        [g, a, b, k]
    }
}

fn shape([_, a, b, _]: Record, ones: &[bool]) -> u8 {
    match (ones[a as usize], ones[b as usize]) {
        (true, true) => 0,
        (true, false) | (false, true) => 1,
        (false, false) if a == b => 2,
        _ => 3,
    }
}

fn difference(a: Record, b: Record) -> TermDelta {
    TermDelta {
        g: b[0].wrapping_sub(a[0]),
        h: [b[1].wrapping_sub(a[1]), b[2].wrapping_sub(a[2])],
        k_index: b[3],
    }
}

/// Extract translated cores; every excluded term goes to the ordinary residual
/// stream. No patch opcodes, no semantic deletion, and no new runtime format.
#[derive(Default)]
pub struct CoreTrace {
    /// Usage bits: core interior=1, core boundary=2, residual=4.
    pub roles: Vec<u8>,
    /// 0=core, 1=unmatched program, 2=one-term program, 3=shape mismatch,
    /// 4=singleton translation class, 5=unselected nonsingleton class.
    pub reasons: Vec<u8>,
}

pub(super) fn core_layer<F: SerializableField>(
    nw: usize,
    logw: usize,
    groups: Vec<Group>,
    ones: &[bool],
    all_classes: bool,
    trace: Option<&mut CoreTrace>,
) -> Layer<F> {
    core_layer_fine(nw, logw, groups, ones, all_classes, trace, None)
}

fn core_layer_fine<F: SerializableField>(
    nw: usize,
    logw: usize,
    groups: Vec<Group>,
    ones: &[bool],
    all_classes: bool,
    mut trace: Option<&mut CoreTrace>,
    fine: Option<&str>,
) -> Layer<F> {
    let mut previous = [0; 4];
    let mut runs = Vec::new();
    let mut push = |records: Vec<Record>, reasons: Option<Vec<u8>>| {
        if records.is_empty() {
            return;
        }
        if let Some(t) = trace.as_deref_mut() {
            if let Some(reasons) = reasons {
                assert_eq!(records.len(), reasons.len());
                t.roles.extend(std::iter::repeat_n(4, records.len()));
                t.reasons.extend(reasons);
            } else {
                t.roles.push(2);
                t.roles.extend(std::iter::repeat_n(1, records.len() - 1));
                t.reasons.extend(std::iter::repeat_n(0, records.len()));
            }
        }
        runs.push(
            records
                .into_iter()
                .map(|r| {
                    let d = difference(previous, r);
                    previous = r;
                    d
                })
                .collect(),
        );
    };
    let mut shared_terms = 0;
    let mut residual_terms = 0;
    let mut cores = 0;
    for kind in 0..4 {
        let mut residual = Vec::new();
        for group in &groups {
            if group.maps.len() < 2 || group.program.len() < 2 {
                for map in &group.maps {
                    residual.extend(
                        group
                            .program
                            .iter()
                            .map(|&r| group.expand(r, map))
                            .filter(|&r| shape(r, ones) == kind)
                            .map(|r| (r, if group.maps.len() < 2 { 1 } else { 2 })),
                    );
                }
                continue;
            }
            let instances: Vec<Vec<_>> = group
                .maps
                .iter()
                .map(|map| {
                    group
                        .program
                        .iter()
                        .map(|&r| group.expand(r, map))
                        .collect()
                })
                .collect();
            let mut ids = HashMap::<Vec<u32>, usize>::new();
            let mut classes = Vec::<Vec<usize>>::new();
            let mut reasons = vec![4; group.program.len()];
            for j in 0..group.program.len() {
                if instances.iter().any(|rows| shape(rows[j], ones) != kind) {
                    reasons[j] = 3;
                    continue;
                }
                // Two terms may share a core iff their coordinate translations
                // relative to instance zero agree in EVERY instance. This is an
                // exact equality of vectors, not a hash-only match or a tolerance.
                let reference = instances[0][j];
                let signature: Vec<_> = instances
                    .iter()
                    .skip(1)
                    .flat_map(|rows| {
                        (0..3).map(move |axis| rows[j][axis].wrapping_sub(reference[axis]))
                    })
                    .collect();
                let next = classes.len();
                let id = *ids.entry(signature).or_insert_with(|| {
                    classes.push(Vec::new());
                    next
                });
                classes[id].push(j);
            }
            let selected: Vec<_> = if all_classes {
                (0..classes.len())
                    .filter(|&i| classes[i].len() >= 2)
                    .collect()
            } else {
                classes
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| c.len() >= 2)
                    .max_by_key(|(i, c)| (c.len(), std::cmp::Reverse(*i)))
                    .map(|(i, _)| vec![i])
                    .unwrap_or_default()
            };
            let mut retained = vec![false; group.program.len()];
            for class in classes.iter().filter(|c| c.len() >= 2) {
                for &j in class {
                    reasons[j] = 5;
                }
            }
            for i in selected {
                let js = &classes[i];
                for &j in js {
                    retained[j] = true;
                }
                cores += 1;
                let expected: Vec<_> = js
                    .windows(2)
                    .map(|p| difference(instances[0][p[0]], instances[0][p[1]]))
                    .collect();
                for rows in &instances {
                    let body: Vec<_> = js.iter().map(|&j| rows[j]).collect();
                    assert!(body
                        .windows(2)
                        .zip(&expected)
                        .all(|(p, d)| difference(p[0], p[1]) == *d));
                    shared_terms += body.len();
                    push(body, None);
                }
            }
            for rows in instances {
                residual.extend(rows.into_iter().enumerate().filter_map(|(j, r)| {
                    (!retained[j] && shape(r, ones) == kind).then_some((r, reasons[j]))
                }));
            }
        }
        // Collect exceptions across the layer so they do not interrupt cores.
        // Keep output-major order, with coefficient index breaking exact ties.
        residual.sort_unstable_by_key(|(r, _)| {
            (std::cmp::Reverse(r[0]), std::cmp::Reverse(r[2]), r[1], r[3])
        });
        if let Some(mode) = fine {
            let (extracted, remaining) = fine_residual(residual, mode);
            for records in extracted {
                shared_terms += records.len();
                push(records, None);
            }
            residual = remaining;
        }
        residual_terms += residual.len();
        let (records, reasons) = residual.into_iter().unzip();
        push(records, Some(reasons));
    }
    println!("CORE_LAYER all_classes={all_classes} cores={cores} shared_terms={shared_terms} residual_terms={residual_terms}");
    let tokens = (0..runs.len() as u32).collect();
    Layer::new_compressed(nw, logw, runs, tokens)
}

/// Find exact translated fragments without requiring enclosing components to
/// match. All coordinates and coefficients participate in the exact key.
fn fine_residual(residual: Vec<(Record, u8)>, mode: &str) -> (Vec<Vec<Record>>, Vec<(Record, u8)>) {
    let (by_gate, width) = match mode {
        "gate" => (true, usize::MAX),
        "gate8" => (true, 8),
        "gate2" => (true, 2),
        "window32" => (false, 32),
        "window128" => (false, 128),
        _ => panic!("unknown fine extraction mode {mode}"),
    };
    let mut ids = HashMap::<Vec<Record>, usize>::new();
    let mut families = Vec::<Vec<std::ops::Range<usize>>>::new();
    let mut at = 0;
    while at < residual.len() {
        // Only the unmatched-program residue is searched. Existing template
        // interiors, and known cheap one-term/translation residues stay intact.
        if residual[at].1 != 1 {
            at += 1;
            continue;
        }
        let mut end = at + 1;
        while end < residual.len()
            && end - at < width
            && residual[end].1 == 1
            && (!by_gate || residual[end].0[0] == residual[at].0[0])
        {
            end += 1;
        }
        if end - at >= 2 {
            let base = residual[at].0;
            let key: Vec<_> = residual[at..end]
                .iter()
                .map(|(r, _)| {
                    [
                        r[0].wrapping_sub(base[0]),
                        r[1].wrapping_sub(base[1]),
                        r[2].wrapping_sub(base[2]),
                        r[3],
                    ]
                })
                .collect();
            let next = families.len();
            let id = *ids.entry(key).or_insert_with(|| {
                families.push(Vec::new());
                next
            });
            families[id].push(at..end);
        }
        at = end;
    }
    let mut used = vec![false; residual.len()];
    let mut extracted = Vec::new();
    let mut family_count = 0;
    for family in families.iter().filter(|f| f.len() >= 2) {
        family_count += 1;
        let reference: Vec<_> = residual[family[0].clone()]
            .windows(2)
            .map(|p| difference(p[0].0, p[1].0))
            .collect();
        for range in family {
            let records: Vec<_> = residual[range.clone()].iter().map(|r| r.0).collect();
            assert!(records
                .windows(2)
                .zip(&reference)
                .all(|(p, d)| difference(p[0], p[1]) == *d));
            for i in range.clone() {
                assert!(!used[i]);
                used[i] = true;
            }
            extracted.push(records);
        }
    }
    let shared = used.iter().filter(|&&v| v).count();
    println!(
        "FINE_RESIDUAL mode={mode} families={family_count} runs={} extracted={shared} remaining={}",
        extracted.len(),
        residual.len() - shared
    );
    let remaining = residual
        .into_iter()
        .zip(used)
        .filter_map(|(r, used)| (!used).then_some(r))
        .collect();
    (extracted, remaining)
}

/// Expand maps only in the offline scheduler. The output has ordinary absolute
/// coordinate deltas and preserves each instance boundary as an initial run.
pub(super) fn ordered_layer<F: SerializableField>(
    nw: usize,
    logw: usize,
    groups: Vec<Group>,
    ones: &[bool],
    traversal: &str,
) -> Layer<F> {
    if let Some(mode) = traversal.strip_prefix("shape_fine_") {
        return core_layer_fine(nw, logw, groups, ones, true, None, Some(mode));
    }
    if matches!(traversal, "shape_core" | "shape_classes") {
        return core_layer(nw, logw, groups, ones, traversal == "shape_classes", None);
    }
    let shape_outer = traversal.starts_with("shape_");
    let interleave = traversal.ends_with("terms");
    assert!(matches!(
        traversal,
        "instances" | "terms" | "shape_instances" | "shape_terms"
    ));
    let mut previous = [0u32; 3];
    let mut runs = Vec::new();
    let mut push = |records: Vec<Record>| {
        if records.is_empty() {
            return;
        }
        let run = records
            .into_iter()
            .map(|[g, a, b, k]| {
                let delta = TermDelta {
                    g: g.wrapping_sub(previous[0]),
                    h: [a.wrapping_sub(previous[1]), b.wrapping_sub(previous[2])],
                    k_index: k,
                };
                previous = [g, a, b];
                delta
            })
            .collect();
        runs.push(run);
    };
    for shape in 0..if shape_outer { 4 } else { 1 } {
        for group in &groups {
            let expand = |[g, a, b, k]: Record, map: &[u32]| {
                let [g, a, b, k] = group.expand([g, a, b, k], map);
                let kind = if shape_outer {
                    match (ones[a as usize], ones[b as usize]) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        (false, false) if a == b => 2,
                        _ => 3,
                    }
                } else {
                    0
                };
                (kind == shape).then_some([g, a, b, k])
            };
            if interleave && group.maps.len() > 1 {
                for &record in &group.program {
                    push(
                        group
                            .maps
                            .iter()
                            .filter_map(|map| expand(record, map))
                            .collect(),
                    );
                }
            } else {
                for map in &group.maps {
                    push(
                        group
                            .program
                            .iter()
                            .filter_map(|&record| expand(record, map))
                            .collect(),
                    );
                }
            }
        }
    }
    let tokens = (0..runs.len() as u32).collect();
    Layer::new_compressed(nw, logw, runs, tokens)
}

pub fn records<F: SerializableField>(layer: &Layer<F>) -> Vec<Record> {
    let mut result = Vec::with_capacity(layer.num_terms());
    let mut previous = [0u32; 3];
    layer.for_each_delta(|d| {
        previous[0] = previous[0].wrapping_add(d.g);
        previous[1] = previous[1].wrapping_add(d.h[0]);
        previous[2] = previous[2].wrapping_add(d.h[1]);
        result.push([previous[0], previous[1], previous[2], d.k_index]);
    });
    result
}

pub fn convert<F: SerializableField + AlgebraicField>(
    f: &F,
    c: &Circuit<F>,
    window: usize,
    affine: bool,
    order: usize,
    components: usize,
    traversal: &str,
) -> Circuit<F> {
    assert!(window > 0);
    let mut layers = Vec::new();
    let mut nv = c.raw.noutput;
    let ones = ones(f, c);
    let coefficients: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    let mut component_count = 0;
    let mut largest_component_terms = 0;
    for (depth, layer) in c.raw.layers.iter().enumerate() {
        let mut terms = records(layer);
        let mut component = vec![0; nv];
        if components != 0 {
            let mut parent: Vec<_> = (0..nv + layer.nw()).collect();
            for &[g, a, b, _] in &terms {
                if depth + 1 == c.raw.layers.len() {
                    continue;
                } // original inputs are ports
                if components == 1 && ones[depth][g as usize] {
                    continue;
                }
                for h in [a, b] {
                    if components == 1 && ones[depth + 1][h as usize] {
                        continue;
                    }
                    let x = root(&mut parent, g as usize);
                    let y = root(&mut parent, nv + h as usize);
                    parent[x.max(y)] = x.min(y);
                }
            }
            let mut minimum = vec![usize::MAX; parent.len()];
            for i in 0..parent.len() {
                let r = root(&mut parent, i);
                minimum[r] = minimum[r].min(if i < nv { i } else { i - nv });
            }
            // Min wire ID, with root ID breaking ties between the two sides.
            let mut roots: Vec<_> = (0..nv).map(|i| root(&mut parent, i)).collect();
            roots.sort_unstable_by_key(|&r| (minimum[r], r));
            roots.dedup();
            let rank: HashMap<_, _> = roots.into_iter().enumerate().map(|(i, r)| (r, i)).collect();
            for (i, value) in component.iter_mut().enumerate() {
                *value = rank[&root(&mut parent, i)];
            }
            let mut sizes = HashMap::<usize, usize>::new();
            for t in &terms {
                *sizes.entry(component[t[0] as usize]).or_default() += 1;
            }
            component_count += sizes.len();
            largest_component_terms =
                largest_component_terms.max(sizes.values().copied().max().unwrap_or(0));
        }
        // Gate-aligned windows; a gate is never split across templates.
        match order {
            0 | 2 | 3 | 4 => terms.sort_unstable_by_key(|t| (component[t[0] as usize], *t)),
            1 => {
                terms.sort_unstable_by_key(|t| (component[t[0] as usize], [t[0], t[3], t[2], t[1]]))
            }
            _ => panic!("unknown template order"),
        }
        let mut ends = Vec::new();
        let mut gates = 0;
        for i in 0..terms.len() {
            if i + 1 == terms.len() || terms[i][0] != terms[i + 1][0] {
                gates += 1;
                let boundary = i + 1 == terms.len()
                    || component[terms[i][0] as usize] != component[terms[i + 1][0] as usize];
                if gates == window || boundary {
                    ends.push(i + 1);
                    gates = 0;
                }
            }
        }
        if ends.last() != Some(&terms.len()) && !terms.is_empty() {
            ends.push(terms.len());
        }
        type Key = (Vec<Record>, usize, usize);
        let mut ids = HashMap::<Key, usize>::new();
        let mut groups: Vec<(Key, Vec<Vec<u32>>)> = Vec::new();
        let mut start = 0;
        for end in ends {
            let chunk = &terms[start..end];
            start = end;
            let (mut local, map, ng) = if affine {
                let bases: Vec<_> = (0..3)
                    .map(|j| {
                        chunk
                            .iter()
                            .map(|t| t[j])
                            .filter(|&v| j == 0 || v != 0)
                            .min()
                            .unwrap_or(0)
                    })
                    .collect();
                let local: Vec<_> = chunk
                    .iter()
                    .map(|t| {
                        [
                            t[0] - bases[0],
                            if t[1] == 0 { 0 } else { t[1] - bases[1] + 1 },
                            if t[2] == 0 { 0 } else { t[2] - bases[2] + 1 },
                            t[3],
                        ]
                    })
                    .collect();
                (local, bases, 1)
            } else {
                let mut gs: Vec<_> = chunk.iter().map(|t| t[0]).collect();
                gs.dedup();
                let mut hs: Vec<_> = chunk.iter().flat_map(|t| [t[1], t[2]]).collect();
                hs.sort_unstable();
                hs.dedup();
                let local: Vec<_> = chunk
                    .iter()
                    .map(|t| {
                        [
                            gs.binary_search(&t[0]).unwrap() as u32,
                            hs.binary_search(&t[1]).unwrap() as u32,
                            hs.binary_search(&t[2]).unwrap() as u32,
                            t[3],
                        ]
                    })
                    .collect();
                let ng = gs.len();
                gs.extend(hs);
                (local, gs, ng)
            };
            sort_local(&mut local, order);
            if order == 4 {
                let kind = |t: &Record| {
                    let wire = |j: usize| {
                        if affine {
                            if t[j] == 0 {
                                0
                            } else {
                                map[j] + t[j] - 1
                            }
                        } else {
                            map[ng + t[j] as usize]
                        }
                    };
                    let one = |j: usize| ones[depth + 1][wire(j) as usize];
                    match (one(1), one(2)) {
                        (true, true) => 0,
                        (true, false) | (false, true) => 1,
                        (false, false) if wire(1) == wire(2) => 2,
                        _ => 3,
                    }
                };
                local.sort_unstable_by(|a, b| {
                    kind(a)
                        .cmp(&kind(b))
                        .then(b[0].cmp(&a[0]))
                        .then(b[2].cmp(&a[2]))
                        .then(a[1].cmp(&b[1]))
                        .then_with(|| coefficients[a[3] as usize].cmp(&coefficients[b[3] as usize]))
                });
            }
            let key = (local, ng, map.len());
            let id = *ids.entry(key.clone()).or_insert_with(|| {
                let i = groups.len();
                groups.push((key, Vec::new()));
                i
            });
            groups[id].1.push(map);
        }
        let groups = groups
            .into_iter()
            .map(|((program, ng, _), maps)| Group {
                program,
                ng,
                maps,
                affine,
                canonical_h: false,
            })
            .collect();
        layers.push(ordered_layer(
            layer.nw(),
            layer.logw(),
            groups,
            &ones[depth + 1],
            traversal,
        ));
        nv = layer.nw();
    }
    let raw = RawCircuit {
        ninput: c.raw.ninput,
        npublic_input: c.raw.npublic_input,
        noutput: c.raw.noutput,
        logv: c.raw.logv,
        subfield_boundary: c.raw.subfield_boundary,
        constants: c.raw.constants.clone(),
        layers,
    };
    // Same existing ID algorithm, applied to the new stored traversal. No claim
    // that the legacy order-sensitive ID survives regrouping.
    let id = core_proto::circuit::compute_id(f, &raw);
    if components != 0 {
        println!("ORDER_COMPONENTS mode={components} count={component_count} largest_terms={largest_component_terms}");
    }
    Circuit { raw, id }
}

pub(super) fn sort_local(local: &mut [Record], order: usize) {
    match order {
        2 => local.sort_unstable_by(|a, b| {
            let spread = |x: u32| {
                let mut r = 0u64;
                for bit in 0..32 {
                    r |= u64::from((x >> bit) & 1) << (2 * bit);
                }
                r
            };
            (spread(a[1]) | spread(a[2]) << 1, a[0], a[3]).cmp(&(
                spread(b[1]) | spread(b[2]) << 1,
                b[0],
                b[3],
            ))
        }),
        3 => local.sort_unstable_by_key(|t| {
            (
                t[1] != 0,
                std::cmp::Reverse(t[0]),
                std::cmp::Reverse(t[2]),
                t[1],
                t[3],
            )
        }),
        _ => (),
    }
}

pub fn assert_same<F: SerializableField>(a: &Circuit<F>, b: &Circuit<F>) {
    assert_eq!(a.raw.layers.len(), b.raw.layers.len());
    for (a, b) in a.raw.layers.iter().zip(&b.raw.layers) {
        let mut x = records(a);
        let mut y = records(b);
        x.sort_unstable();
        y.sort_unstable();
        assert_eq!(x, y);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type F = runtime_algebra::gf2_128::Gf2_128Field;

    #[test]
    fn fine_fragments_match_inside_different_enclosing_programs() {
        let input = vec![
            ([8, 10, 20, 1], 1),
            ([8, 11, 22, 2], 1),
            ([7, 15, 25, 8], 1),
            ([6, 30, 40, 1], 1),
            ([6, 31, 42, 2], 1),
            ([5, 1, 1, 3], 2),
        ];
        let (runs, tail) = fine_residual(input.clone(), "gate");
        assert_eq!(runs.len(), 2);
        assert_eq!(runs[0].len(), 2);
        assert_eq!(
            difference(runs[0][0], runs[0][1]),
            difference(runs[1][0], runs[1][1])
        );
        let mut expected: Vec<_> = input.iter().map(|r| r.0).collect();
        let mut actual: Vec<_> = runs
            .into_iter()
            .flatten()
            .chain(tail.into_iter().map(|r| r.0))
            .collect();
        expected.sort_unstable();
        actual.sort_unstable();
        assert_eq!(actual, expected);
    }

    #[test]
    fn fine_matching_keeps_coefficients_and_duplicate_multiplicities() {
        let input = vec![
            ([8, 10, 20, 1], 1),
            ([8, 10, 20, 1], 1),
            ([6, 30, 40, 1], 1),
            ([6, 30, 40, 2], 1),
        ];
        for mode in ["gate", "gate8", "gate2", "window32", "window128"] {
            let (runs, tail) = fine_residual(input.clone(), mode);
            assert!(runs.is_empty());
            assert_eq!(tail, input);
        }
    }

    fn example() -> Group {
        Group {
            // Wire 1 does not translate. Keep its term in the residual stream.
            // The duplicate of wire 0 and its assertion-marker coefficient stay.
            program: vec![[2, 2, 2, 1], [1, 1, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
            ng: 3,
            maps: vec![vec![10, 11, 12, 20, 21, 22], vec![30, 31, 32, 40, 99, 42]],
            affine: false,
            canonical_h: true,
        }
    }

    #[test]
    fn cores_share_deltas_and_preserve_exception_terms_and_duplicates() {
        let group = example();
        let ones = vec![false; 100];
        let mut expected: Vec<_> = group
            .maps
            .iter()
            .flat_map(|map| group.program.iter().map(|&r| group.expand(r, map)))
            .collect();
        expected.sort_unstable();
        for traversal in ["shape_core", "shape_classes"] {
            let layer = ordered_layer::<F>(100, 7, vec![group.clone()], &ones, traversal);
            let mut actual = records(&layer);
            actual.sort_unstable();
            assert_eq!(actual, expected);
            let a = &layer.delta_segments()[layer.delta_tokens()[0] as usize];
            let b = &layer.delta_segments()[layer.delta_tokens()[1] as usize];
            assert_eq!(a.len(), 3);
            assert_eq!(a[1..], b[1..]);
            assert_eq!(layer.num_terms(), 8);
        }
    }

    #[test]
    fn audit_trace_preserves_stream_and_separates_boundaries() {
        let ones = vec![false; 100];
        let expected = ordered_layer::<F>(100, 7, vec![example()], &ones, "shape_classes");
        let mut trace = CoreTrace::default();
        let actual = core_layer::<F>(100, 7, vec![example()], &ones, true, Some(&mut trace));
        assert_eq!(records(&actual), records(&expected));
        assert_eq!(actual.deltas(), expected.deltas());
        assert_eq!(actual.delta_segments(), expected.delta_segments());
        assert_eq!(actual.delta_tokens(), expected.delta_tokens());
        assert_eq!(trace.roles, [2, 1, 1, 2, 1, 1, 4, 4]);
        assert_eq!(trace.reasons, [0, 0, 0, 0, 0, 0, 4, 4]);
    }

    #[test]
    fn shape_mismatches_are_not_dropped_or_shared() {
        let group = example();
        let mut ones = vec![false; 100];
        ones[99] = true;
        let mut expected: Vec<_> = group
            .maps
            .iter()
            .flat_map(|map| group.program.iter().map(|&r| group.expand(r, map)))
            .collect();
        expected.sort_unstable();
        for traversal in ["shape_core", "shape_classes"] {
            let layer = ordered_layer::<F>(100, 7, vec![group.clone()], &ones, traversal);
            let mut actual = records(&layer);
            actual.sort_unstable();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn multiple_translation_classes_can_be_shared_without_overlap() {
        let group = Group {
            program: vec![[3, 3, 3, 1], [2, 2, 2, 1], [1, 1, 1, 1], [0, 0, 0, 1]],
            ng: 4,
            maps: vec![
                vec![10, 11, 12, 13, 20, 21, 22, 23],
                vec![30, 31, 32, 33, 40, 61, 42, 63],
            ],
            affine: false,
            canonical_h: true,
        };
        let ones = vec![false; 100];
        let single = ordered_layer::<F>(100, 7, vec![group.clone()], &ones, "shape_core");
        let multiple = ordered_layer::<F>(100, 7, vec![group.clone()], &ones, "shape_classes");
        let mut a = records(&single);
        let mut b = records(&multiple);
        a.sort_unstable();
        b.sort_unstable();
        assert_eq!(a, b);
        assert_eq!(a.len(), 8);
        assert_eq!(single.delta_tokens().len(), 3); // two core instances, residual
        assert_eq!(multiple.delta_tokens().len(), 4); // two instances of both cores
    }
}
