// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Packed Keccak-f[1600] for scalar SHAKE128/256 sponge frontends. Each bit
//! plane holds 128 independent permutations. Sponge padding and links remain
//! scalar constraints; initial/final state bits are shared commitment cells.
use sha2::{Digest, Sha256};

use crate::{
    circuits::keccak::{ROTC, ROUNDC},
    core::{
        algebra::AlgebraicField,
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::gf2_128::Gf2_128Field as F,
        v2::simd_sumcheck::{AffineInput, Program},
    },
    util::ceil_log2,
};
pub struct SharedShake {
    pub program: Program,
    placements: Vec<(usize, u8)>,
    batches: usize,
    scalar_words: usize,
    links: Vec<(Vec<usize>, Vec<usize>)>,
}
#[cfg(test)]
mod tests;
#[cfg_attr(
    not(any(test, feature = "compiler", feature = "prover")),
    allow(dead_code)
)]
fn at(x: usize, y: usize, z: usize) -> usize {
    (x * 5 + y) * 64 + z
}
impl SharedShake {
    /// Built by the compiler; proof roles receive the finished program.
    #[cfg_attr(not(any(test, feature = "compiler")), allow(dead_code))]
    pub fn new(private: usize, links: Vec<(Vec<usize>, Vec<usize>)>) -> Result<Self, String> {
        if links.is_empty() {
            return Err("SIMD SHAKE requires permutations".into());
        }
        let batches = links.len().div_ceil(128);
        let mut placements = vec![(usize::MAX, 0); private];
        for (permutation, (a, b)) in links.iter().enumerate() {
            for (end, list) in [a, b].iter().enumerate() {
                if list.len() != 1600 {
                    return Err("SIMD SHAKE endpoint width".into());
                }
                for (j, &input) in list.iter().enumerate() {
                    if input >= private || placements[input].0 != usize::MAX {
                        return Err("SIMD SHAKE source overlap".into());
                    }
                    placements[input] = (
                        permutation / 128 * 3200 + end * 1600 + j,
                        (permutation % 128) as u8,
                    );
                }
            }
        }
        let mut word = batches * 3200;
        let mut bit = 0;
        for location in &mut placements {
            if location.0 == usize::MAX {
                *location = (word, bit);
                bit += 1;
                if bit == 128 {
                    word += 1;
                    bit = 0;
                }
            }
        }
        let scalar_words = word + usize::from(bit != 0);
        let real = scalar_words + batches * 23 * 1600;
        let state = |batch: usize, round: usize, j: usize| match round {
            0 => batch * 3200 + j,
            24 => batch * 3200 + 1600 + j,
            _ => scalar_words + batch * 23 * 1600 + (round - 1) * 1600 + j,
        };
        let mut forms = vec![];
        let mut q = vec![];
        let mut l = vec![];
        let mut k = vec![];
        for batch in 0..batches {
            for (round, &round_constant) in ROUNDC.iter().enumerate() {
                let base = forms.len();
                let mut b = vec![
                    AffineInput {
                        vars: vec![],
                        constant: false
                    };
                    1600
                ];
                for x in 0..5 {
                    for y in 0..5 {
                        for z in 0..64 {
                            let mut vars = vec![state(batch, round, at(x, y, z))];
                            for yy in 0..5 {
                                vars.push(state(batch, round, at((x + 4) % 5, yy, z)));
                                vars.push(state(batch, round, at((x + 1) % 5, yy, (z + 63) % 64)));
                            }
                            b[at(y, (2 * x + 3 * y) % 5, (z + ROTC[x][y]) % 64)] = AffineInput {
                                vars,
                                constant: false,
                            };
                        }
                    }
                }
                forms.extend(b);
                for x in 0..5 {
                    for y in 0..5 {
                        for z in 0..64 {
                            let g = (batch * 24 * 1600 + round * 1600 + at(x, y, z)) as u32;
                            q.push(Quadratic {
                                g,
                                l: (real + base + at((x + 1) % 5, y, z)) as u32,
                                r: (real + base + at((x + 2) % 5, y, z)) as u32,
                                k: 0,
                            });
                            for wire in [
                                state(batch, round + 1, at(x, y, z)),
                                real + base + at(x, y, z),
                                real + base + at((x + 2) % 5, y, z),
                            ] {
                                l.push(Linear {
                                    g,
                                    l: wire as u32,
                                    k: 0,
                                });
                            }
                            if x == 0 && y == 0 && round_constant >> z & 1 != 0 {
                                k.push(Constant { g, k: 0 });
                            }
                        }
                    }
                }
            }
        }
        let outputs = batches * 24 * 1600;
        for i in (1..q.len()).rev() {
            q[i].g = q[i].g.wrapping_sub(q[i - 1].g);
            q[i].l = q[i].l.wrapping_sub(q[i - 1].l);
            q[i].r = q[i].r.wrapping_sub(q[i - 1].r);
        }
        for i in (1..l.len()).rev() {
            l[i].g = l[i].g.wrapping_sub(l[i - 1].g);
            l[i].l = l[i].l.wrapping_sub(l[i - 1].l);
        }
        for i in (1..k.len()).rev() {
            k[i].g = k[i].g.wrapping_sub(k[i - 1].g);
        }
        fn stream<T>(deltas: Vec<T>) -> Stream<T> {
            let n = deltas.len();
            Stream {
                deltas,
                segments: vec![(0..n as u32).collect::<Vec<_>>()].into(),
                tokens: vec![0],
            }
        }
        let f = F::new();
        let raw = RawCircuitBuilder {
            ninput: real + forms.len(),
            npublic_input: 0,
            noutput: outputs,
            logv: ceil_log2(outputs),
            constants: vec![f.one()],
            layers: vec![Layer::new(
                real + forms.len(),
                stream(q),
                stream(l),
                stream(k),
            )],
        }
        .build();
        let c = Circuit::from_raw(&f, raw);
        let mut hash = Sha256::new();
        hash.update(b"SHAKE128-256/shared-Keccak-bit-layout/v1");
        hash.update((private as u64).to_le_bytes());
        for &(placed_word, placed_bit) in &placements {
            hash.update((placed_word as u64).to_le_bytes());
            hash.update([placed_bit]);
        }
        let program = Program::new(c, real, forms, hash.finalize().into())?;
        Ok(Self {
            program,
            placements,
            batches,
            scalar_words,
            links,
        })
    }
    pub fn placements(&self) -> &[(usize, u8)] {
        &self.placements
    }
    pub fn metadata_bytes(&self) -> Vec<u8> {
        let mut out = self.program.metadata_bytes();
        for n in [
            self.placements.len(),
            self.batches,
            self.scalar_words,
            self.links.len(),
        ] {
            out.extend((n as u64).to_le_bytes());
        }
        let mut previous = 0i64;
        for (a, b) in &self.links {
            for &n in a.iter().chain(b) {
                let d = n as i64 - previous;
                previous = n as i64;
                let mut v = ((d << 1) ^ (d >> 63)) as u64;
                while v >= 128 {
                    out.push((v as u8 & 127) | 128);
                    v >>= 7;
                }
                out.push(v as u8);
            }
        }
        out
    }
}

cfg_prover! {mod prover;}
