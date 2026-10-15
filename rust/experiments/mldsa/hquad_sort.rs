// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Competing Morton preparation implementations, retained for reproducibility.
use core_algebra::SerializableField;
use core_proto::Layer;
use runtime_algebra::RuntimeField;
use runtime_sumcheck::{hquad::HCorner, HQuad};
use std::cmp::Ordering;

pub const NAMES: &[&str] = &[
    "index-cycle",
    "index-gather",
    "weighted-coordinates",
    "weighted-key",
    "weighted-key-stable",
    "raw-coordinates",
    "raw-key",
    "raw-key-stable",
    "raw-packed",
    "soa-quicksort",
    "index-key-gather",
    "raw-key-tight",
    "raw-key-stable-tight",
    "raw-key-grouped",
    "index-key-gather-tight",
    "weighted-indirect",
    "raw-ranges",
    "weighted-indirect-lazy-key",
];

fn spread(value: u32) -> u64 {
    let mut x = value as u64;
    x = (x | (x << 16)) & 0x0000ffff0000ffff;
    x = (x | (x << 8)) & 0x00ff00ff00ff00ff;
    x = (x | (x << 4)) & 0x0f0f0f0f0f0f0f0f;
    x = (x | (x << 2)) & 0x3333333333333333;
    (x | (x << 1)) & 0x5555555555555555
}
fn key(h: [u32; 2]) -> u64 {
    spread(h[0]) | (spread(h[1]) << 1)
}
fn compact(mut x: u64) -> u32 {
    x &= 0x5555555555555555;
    x = (x | (x >> 1)) & 0x3333333333333333;
    x = (x | (x >> 2)) & 0x0f0f0f0f0f0f0f0f;
    x = (x | (x >> 4)) & 0x00ff00ff00ff00ff;
    x = (x | (x >> 8)) & 0x0000ffff0000ffff;
    (x | (x >> 16)) as u32
}
fn coords(k: u64) -> [u32; 2] {
    [compact(k), compact(k >> 1)]
}
fn cmp(a: [u32; 2], b: [u32; 2]) -> Ordering {
    if (a[1] ^ b[1]).leading_zeros() <= (a[0] ^ b[0]).leading_zeros() {
        a[1].cmp(&b[1]).then(a[0].cmp(&b[0]))
    } else {
        a[0].cmp(&b[0]).then(a[1].cmp(&b[1]))
    }
}
fn weight<const W: usize, F: RuntimeField<W>>(k: &F::E, g: &F::E, beta: &F::E, f: &F) -> F::E {
    f.mulf(if f.is_zero(k) { beta } else { k }, g)
}
fn append<const W: usize, F: RuntimeField<W>>(q: &mut HQuad<W, F>, h: [u32; 2], v: F::E, f: &F) {
    if q.hc.last().is_some_and(|p| p.h == h) {
        f.add(q.vc.last_mut().unwrap(), &v);
    } else {
        q.hc.push(HCorner { h });
        q.vc.push(v);
    }
}
fn empty<const W: usize, F: RuntimeField<W>>(cap: usize) -> HQuad<W, F> {
    HQuad {
        hc: Vec::with_capacity(cap),
        vc: Vec::with_capacity(cap),
    }
}
fn weighted<const W: usize, F: RuntimeField<W> + SerializableField>(
    l: &Layer<F>,
    c: &[F::E],
    g: &[F::E],
    beta: &F::E,
    f: &F,
) -> HQuad<W, F> {
    let mut q = empty(l.nterms_after_bind_g());
    l.for_each_term(c, |t| {
        append(
            &mut q,
            [t.h0, t.h1],
            weight(&t.k, &g[t.g as usize], beta, f),
            f,
        )
    });
    q
}
fn coalesce<const W: usize, F: RuntimeField<W>>(q: &mut HQuad<W, F>, f: &F) {
    let mut n = 0;
    for i in 0..q.hc.len() {
        if n > 0 && q.hc[n - 1].h == q.hc[i].h {
            let v = q.vc[i].clone();
            f.add(&mut q.vc[n - 1], &v);
        } else {
            q.hc[n] = q.hc[i];
            q.vc.swap(n, i);
            n += 1;
        }
    }
    q.hc.truncate(n);
    q.vc.truncate(n);
}

#[derive(Clone, Copy)]
struct Raw {
    h: [u32; 2],
    g: u32,
    k: u32,
}
#[derive(Clone, Copy)]
struct Keyed {
    key: u64,
    g: u32,
    k: u32,
}
fn raw<F: SerializableField>(l: &Layer<F>) -> Vec<Raw> {
    let mut v = Vec::with_capacity(l.num_terms());
    for_raw(l, |t| v.push(t));
    v
}
fn for_raw<F: SerializableField>(l: &Layer<F>, mut cb: impl FnMut(Raw)) {
    let mut prev = [0u32; 3];
    l.for_each_delta(|d| {
        prev = [
            prev[0].wrapping_add(d.g),
            prev[1].wrapping_add(d.h[0]),
            prev[2].wrapping_add(d.h[1]),
        ];
        cb(Raw {
            h: [prev[1], prev[2]],
            g: prev[0],
            k: d.k_index,
        });
    });
}

pub fn prepare<const W: usize, F: RuntimeField<W> + SerializableField>(
    name: &str,
    l: &Layer<F>,
    c: &[F::E],
    g: &[F::E],
    beta: &F::E,
    f: &F,
) -> HQuad<W, F> {
    match name {
        "weighted-indirect" | "weighted-indirect-lazy-key" => {
            let initial_cap = l.nterms_after_bind_g();
            let mut values: Vec<F::E> = Vec::with_capacity(initial_cap);
            let mut p: Vec<(u64, usize)> = Vec::with_capacity(initial_cap);
            let mut previous_h = None;
            l.for_each_term(c, |t| {
                let h = [t.h0, t.h1];
                let value = weight(&t.k, &g[t.g as usize], beta, f);
                if name == "weighted-indirect-lazy-key" {
                    if previous_h == Some(h) {
                        f.add(values.last_mut().unwrap(), &value);
                    } else {
                        p.push((key(h), values.len()));
                        values.push(value);
                        previous_h = Some(h);
                    }
                } else {
                    let k = key(h);
                    if p.last().is_some_and(|entry| entry.0 == k) {
                        f.add(values.last_mut().unwrap(), &value);
                    } else {
                        p.push((k, values.len()));
                        values.push(value);
                    }
                }
            });
            p.sort_unstable_by_key(|t| t.0);
            let cap = usize::from(!p.is_empty())
                + p.windows(2).filter(|pair| pair[0].0 != pair[1].0).count();
            let mut out = empty(cap);
            let mut previous = None;
            for (k, i) in p {
                if previous == Some(k) {
                    f.add(out.vc.last_mut().unwrap(), &values[i]);
                } else {
                    out.hc.push(HCorner { h: coords(k) });
                    out.vc.push(values[i].clone());
                    previous = Some(k);
                }
            }
            out
        }
        "raw-ranges" => {
            let mut values: Vec<(u32, u32)> = Vec::with_capacity(l.num_terms());
            let mut p: Vec<Keyed> = Vec::with_capacity(l.nterms_after_bind_g());
            for_raw(l, |t| {
                let k = key(t.h);
                if p.last().is_some_and(|entry| entry.key == k) {
                    p.last_mut().unwrap().k += 1;
                } else {
                    p.push(Keyed {
                        key: k,
                        g: u32::try_from(values.len()).unwrap(),
                        k: 1,
                    });
                }
                values.push((t.g, t.k));
            });
            p.sort_unstable_by_key(|t| t.key);
            let cap = usize::from(!p.is_empty())
                + p.windows(2)
                    .filter(|pair| pair[0].key != pair[1].key)
                    .count();
            let mut out = empty(cap);
            let mut previous = None;
            for t in p {
                let slice = &values[t.g as usize..t.g as usize + t.k as usize];
                let mut value = weight(&c[slice[0].1 as usize], &g[slice[0].0 as usize], beta, f);
                for &(gi, ki) in &slice[1..] {
                    f.add(
                        &mut value,
                        &weight(&c[ki as usize], &g[gi as usize], beta, f),
                    );
                }
                if previous == Some(t.key) {
                    f.add(out.vc.last_mut().unwrap(), &value);
                } else {
                    out.hc.push(HCorner { h: coords(t.key) });
                    out.vc.push(value);
                    previous = Some(t.key);
                }
            }
            out
        }
        "index-key-gather" | "index-key-gather-tight" => {
            let q = weighted(l, c, g, beta, f);
            let mut p: Vec<(u64, usize)> =
                q.hc.iter()
                    .enumerate()
                    .map(|(i, h)| (key(h.h), i))
                    .collect();
            p.sort_unstable_by_key(|t| t.0);
            let cap = if name.ends_with("tight") {
                usize::from(!p.is_empty())
                    + p.windows(2).filter(|pair| pair[0].0 != pair[1].0).count()
            } else {
                q.hc.len()
            };
            let mut out = empty(cap);
            for (_, i) in p {
                append(&mut out, q.hc[i].h, q.vc[i].clone(), f);
            }
            out
        }
        "index-cycle" | "index-gather" => {
            let mut q = weighted(l, c, g, beta, f);
            if q.hc.windows(2).all(|p| cmp(p[0].h, p[1].h).is_le()) {
                return q;
            }
            let mut p: Vec<usize> = (0..q.hc.len()).collect();
            p.sort_unstable_by(|&a, &b| cmp(q.hc[a].h, q.hc[b].h));
            if name == "index-gather" {
                let mut out = empty(q.hc.len());
                for i in p {
                    append(&mut out, q.hc[i].h, q.vc[i].clone(), f);
                }
                out
            } else {
                for start in 0..p.len() {
                    let mut i = start;
                    while p[i] != start {
                        let j = p[i];
                        q.hc.swap(i, j);
                        q.vc.swap(i, j);
                        p[i] = i;
                        i = j;
                    }
                    p[i] = i;
                }
                coalesce(&mut q, f);
                q
            }
        }
        "weighted-coordinates" => {
            let mut v: Vec<([u32; 2], F::E)> = Vec::with_capacity(l.nterms_after_bind_g());
            l.for_each_term(c, |t| {
                let h = [t.h0, t.h1];
                let value = weight(&t.k, &g[t.g as usize], beta, f);
                if v.last().is_some_and(|p| p.0 == h) {
                    f.add(&mut v.last_mut().unwrap().1, &value);
                } else {
                    v.push((h, value));
                }
            });
            v.sort_unstable_by(|a, b| cmp(a.0, b.0));
            v.dedup_by(|a, b| {
                if a.0 == b.0 {
                    f.add(&mut b.1, &a.1);
                    true
                } else {
                    false
                }
            });
            let mut q = empty(v.len());
            for (h, value) in v {
                append(&mut q, h, value, f);
            }
            q
        }
        "weighted-key" | "weighted-key-stable" => {
            let mut v: Vec<(u64, F::E)> = Vec::with_capacity(l.nterms_after_bind_g());
            l.for_each_term(c, |t| {
                let k = key([t.h0, t.h1]);
                let value = weight(&t.k, &g[t.g as usize], beta, f);
                if v.last().is_some_and(|entry| entry.0 == k) {
                    f.add(&mut v.last_mut().unwrap().1, &value);
                } else {
                    v.push((k, value));
                }
            });
            if name == "weighted-key-stable" {
                v.sort_by_key(|p| p.0);
            } else {
                v.sort_unstable_by_key(|p| p.0);
            }
            v.dedup_by(|a, b| {
                if a.0 == b.0 {
                    f.add(&mut b.1, &a.1);
                    true
                } else {
                    false
                }
            });
            let mut q = empty(v.len());
            for (k, value) in v {
                append(&mut q, coords(k), value, f);
            }
            q
        }
        "raw-coordinates" => {
            let mut v = raw(l);
            v.sort_unstable_by(|a, b| cmp(a.h, b.h));
            let mut q = empty(v.len());
            for t in v {
                append(
                    &mut q,
                    t.h,
                    weight(&c[t.k as usize], &g[t.g as usize], beta, f),
                    f,
                );
            }
            q
        }
        "raw-key"
        | "raw-key-stable"
        | "raw-key-tight"
        | "raw-key-stable-tight"
        | "raw-key-grouped" => {
            let mut v: Vec<Keyed> = Vec::with_capacity(l.num_terms());
            for_raw(l, |t| {
                v.push(Keyed {
                    key: key(t.h),
                    g: t.g,
                    k: t.k,
                })
            });
            if name.contains("stable") {
                v.sort_by_key(|t| t.key);
            } else {
                v.sort_unstable_by_key(|t| t.key);
            }
            let cap = if name.ends_with("tight") || name == "raw-key-grouped" {
                usize::from(!v.is_empty())
                    + v.windows(2)
                        .filter(|pair| pair[0].key != pair[1].key)
                        .count()
            } else {
                v.len()
            };
            let mut q = empty(cap);
            let mut previous = None;
            for t in v {
                let value = weight(&c[t.k as usize], &g[t.g as usize], beta, f);
                if name == "raw-key-grouped" {
                    if previous == Some(t.key) {
                        f.add(q.vc.last_mut().unwrap(), &value);
                    } else {
                        q.hc.push(HCorner { h: coords(t.key) });
                        q.vc.push(value);
                        previous = Some(t.key);
                    }
                } else {
                    append(&mut q, coords(t.key), value, f);
                }
            }
            q
        }
        "raw-packed" => {
            let mut v: Vec<u128> = Vec::with_capacity(l.num_terms());
            for_raw(l, |t| {
                v.push(((key(t.h) as u128) << 64) | ((t.g as u128) << 32) | t.k as u128)
            });
            v.sort_unstable();
            let mut q = empty(v.len());
            for t in v {
                append(
                    &mut q,
                    coords((t >> 64) as u64),
                    weight(
                        &c[t as u32 as usize],
                        &g[(t >> 32) as u32 as usize],
                        beta,
                        f,
                    ),
                    f,
                );
            }
            q
        }
        "soa-quicksort" => {
            let mut q = weighted(l, c, g, beta, f);
            let mut keys: Vec<u64> = q.hc.iter().map(|h| key(h.h)).collect();
            // Coordinates are reconstructible from keys; do not permute hc.
            let depth = 2 * (keys.len().max(1).ilog2() as usize);
            sort_soa(&mut keys, &mut q.vc, depth);
            for (hc, k) in q.hc.iter_mut().zip(keys) {
                hc.h = coords(k);
            }
            coalesce(&mut q, f);
            q
        }
        _ => panic!("unknown preparation {name}"),
    }
}

// Safe paired introsort: median pivot, three-way partition, insertion sort for
// small partitions, heapsort fallback. No radix sorting or hash table.
fn sort_soa<E>(k: &mut [u64], v: &mut [E], depth: usize) {
    let n = k.len();
    if n < 24 {
        for i in 1..n {
            let mut j = i;
            while j > 0 && k[j] < k[j - 1] {
                k.swap(j, j - 1);
                v.swap(j, j - 1);
                j -= 1;
            }
        }
        return;
    }
    if depth == 0 {
        fn sift<E>(k: &mut [u64], v: &mut [E], mut r: usize, n: usize) {
            while 2 * r + 1 < n {
                let mut c = 2 * r + 1;
                if c + 1 < n && k[c] < k[c + 1] {
                    c += 1;
                }
                if k[r] >= k[c] {
                    break;
                }
                k.swap(r, c);
                v.swap(r, c);
                r = c;
            }
        }
        for r in (0..n / 2).rev() {
            sift(k, v, r, n);
        }
        for end in (1..n).rev() {
            k.swap(0, end);
            v.swap(0, end);
            sift(k, v, 0, end);
        }
        return;
    }
    let mut sample = [k[0], k[n / 2], k[n - 1]];
    sample.sort_unstable();
    let pivot = sample[1];
    let (mut lo, mut i, mut hi) = (0, 0, n);
    while i < hi {
        if k[i] < pivot {
            k.swap(i, lo);
            v.swap(i, lo);
            lo += 1;
            i += 1;
        } else if k[i] > pivot {
            hi -= 1;
            k.swap(i, hi);
            v.swap(i, hi);
        } else {
            i += 1;
        }
    }
    sort_soa(&mut k[..lo], &mut v[..lo], depth - 1);
    sort_soa(&mut k[hi..], &mut v[hi..], depth - 1);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn keys_and_paired_sort() {
        for a in [0, 1, 2, 3, 65535, 1 << 31, u32::MAX] {
            for b in [0, 1, 2, 3, 65535, 1 << 31, u32::MAX] {
                assert_eq!(coords(key([a, b])), [a, b]);
            }
        }
        for n in [0, 1, 23, 24, 101, 1000] {
            for depth in [0, 20] {
                let mut k: Vec<u64> = (0..n).map(|i| ((i * 71 + 19) % 37) as u64).collect();
                let mut v = k.clone();
                sort_soa(&mut k, &mut v, depth);
                assert!(k.windows(2).all(|p| p[0] <= p[1]));
                assert_eq!(k, v);
            }
        }
    }
}
