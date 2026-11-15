// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Keccak rounds packed across lanes, with authenticated predecessor views.
//! Active round outputs and original permutation starts occupy committed bit
//! planes. Inactive lanes may carry scalar source bits: every round residual
//! projects them away through a public partial bit permutation.
use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use crate::{
    circuits::keccak::{ROTC, ROUNDC},
    core::{
        algebra::AlgebraicField,
        proto::v2::{Circuit, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::gf2_128::Gf2_128Field as F,
        v2::simd_sumcheck::{BitAffineInput, BitPermutation, MappedTerm, Program},
    },
    util::ceil_log2,
};

/// A shared scalar witness with its Keccak rounds packed into 128-bit planes.
///
/// Lane order is permutation-major, then round-major: permutation `p`, round
/// `r` occupies lane `(24*p+r)%128` in batch `(24*p+r)/128`. The source stores
/// all round-output planes before the original permutation-start planes.
/// Unused lanes hold other scalar witness bits and are excluded from round
/// residuals by the public projections. The shared scalar claim still
/// authenticates those bits through their ordinary placements.
pub struct SharedShakeRounds {
    pub program: Program,
    placements: Vec<(usize, u8)>,
    round_batches: usize,
    start_batches: usize,
    links: Vec<(Vec<usize>, Vec<usize>)>,
}
fn at(x: usize, y: usize, z: usize) -> usize {
    (x * 5 + y) * 64 + z
}
fn mask(active: usize) -> u128 {
    if active == 128 {
        u128::MAX
    } else {
        (1u128 << active) - 1
    }
}
fn intern(maps: &mut Vec<BitPermutation>, sources: [Option<u8>; 128]) -> Result<usize, String> {
    let map = BitPermutation::new(sources)?;
    if let Some(index) = maps.iter().position(|m| *m == map) {
        Ok(index)
    } else {
        let index = maps.len();
        maps.push(map);
        Ok(index)
    }
}
impl SharedShakeRounds {
    /// Build trusted setup from disjoint 1600-bit input/output endpoint maps.
    /// Each index addresses the scalar private witness; witness generation
    /// checks the claimed outputs against native Keccak before proving.
    pub fn new(private: usize, links: Vec<(Vec<usize>, Vec<usize>)>) -> Result<Self, String> {
        if links.is_empty() || private > u32::MAX as usize {
            return Err("round-packed SHAKE source dimensions".into());
        }
        let rounds = links
            .len()
            .checked_mul(24)
            .ok_or("Keccak round count overflow")?;
        let round_batches = rounds.div_ceil(128);
        let start_batches = links.len().div_ceil(128);
        let planes = round_batches
            .checked_add(start_batches)
            .and_then(|n| n.checked_mul(1600))
            .ok_or("Keccak source word overflow")?;
        let mut occupied = Vec::with_capacity(planes);
        for batch in 0..round_batches {
            occupied.extend(std::iter::repeat_n(
                mask((rounds - batch * 128).min(128)),
                1600,
            ));
        }
        for batch in 0..start_batches {
            occupied.extend(std::iter::repeat_n(
                mask((links.len() - batch * 128).min(128)),
                1600,
            ));
        }
        let mut placements = vec![(usize::MAX, 0); private];
        for (permutation, (initial, final_state)) in links.iter().enumerate() {
            let final_round = permutation * 24 + 23;
            for (endpoint, indices) in [initial, final_state].iter().enumerate() {
                if indices.len() != 1600 {
                    return Err("round-packed SHAKE endpoint width".into());
                }
                for (bit, &input) in indices.iter().enumerate() {
                    if input >= private || placements[input].0 != usize::MAX {
                        return Err("round-packed SHAKE source overlap".into());
                    }
                    placements[input] = if endpoint == 0 {
                        (
                            (round_batches + permutation / 128) * 1600 + bit,
                            (permutation % 128) as u8,
                        )
                    } else {
                        (final_round / 128 * 1600 + bit, (final_round % 128) as u8)
                    };
                }
            }
        }
        let mut free_word = 0;
        for location in &mut placements {
            if location.0 != usize::MAX {
                continue;
            }
            while free_word < occupied.len() && occupied[free_word] == u128::MAX {
                free_word += 1;
            }
            if free_word == occupied.len() {
                occupied.push(0);
            }
            let lane = (!occupied[free_word]).trailing_zeros() as u8;
            occupied[free_word] |= 1u128 << lane;
            *location = (free_word, lane);
        }
        let real = occupied.len();
        let mut maps = vec![BitPermutation::identity()];
        let mut forms = Vec::new();
        let mut quadratic = Vec::new();
        let mut linear = Vec::new();
        for batch in 0..round_batches {
            let active = (rounds - batch * 128).min(128);
            let output_map = intern(
                &mut maps,
                std::array::from_fn(|lane| (lane < active).then_some(lane as u8)),
            )?;
            // Each destination round reads either its own permutation start,
            // or exactly the preceding round's output, possibly in a prior batch.
            let mut predecessors = BTreeMap::<usize, [Option<u8>; 128]>::new();
            for lane in 0..active {
                let index = batch * 128 + lane;
                let permutation = index / 24;
                let (source_group, source_lane) = if index.is_multiple_of(24) {
                    (round_batches + permutation / 128, permutation % 128)
                } else {
                    ((index - 1) / 128, (index - 1) % 128)
                };
                predecessors.entry(source_group).or_insert([None; 128])[lane] =
                    Some(source_lane as u8);
            }
            let sources = predecessors
                .into_iter()
                .map(|(group, bits)| Ok((group, intern(&mut maps, bits)?)))
                .collect::<Result<Vec<_>, String>>()?;
            let theta_base = forms.len();
            let mut theta = vec![
                BitAffineInput {
                    terms: Vec::new(),
                    constant: 0
                };
                1600
            ];
            for x in 0..5 {
                for y in 0..5 {
                    for z in 0..64 {
                        let mut terms = Vec::with_capacity(11 * sources.len());
                        for &(group, map) in &sources {
                            terms.push(MappedTerm {
                                word: group * 1600 + at(x, y, z),
                                map,
                            });
                            for yy in 0..5 {
                                terms.push(MappedTerm {
                                    word: group * 1600 + at((x + 4) % 5, yy, z),
                                    map,
                                });
                                terms.push(MappedTerm {
                                    word: group * 1600 + at((x + 1) % 5, yy, (z + 63) % 64),
                                    map,
                                });
                            }
                        }
                        theta[at(y, (2 * x + 3 * y) % 5, (z + ROTC[x][y]) % 64)] =
                            BitAffineInput { terms, constant: 0 };
                    }
                }
            }
            forms.extend(theta);
            let mut outputs = Vec::with_capacity(1600);
            for bit in 0..1600 {
                if output_map == 0 {
                    outputs.push(batch * 1600 + bit);
                } else {
                    outputs.push(real + forms.len());
                    forms.push(BitAffineInput {
                        terms: vec![MappedTerm {
                            word: batch * 1600 + bit,
                            map: output_map,
                        }],
                        constant: 0,
                    });
                }
            }
            for x in 0..5 {
                for y in 0..5 {
                    for z in 0..64 {
                        let g = u32::try_from(batch * 1600 + at(x, y, z))
                            .map_err(|_| "Keccak output index")?;
                        let theta_wire = |xx| {
                            u32::try_from(real + theta_base + at(xx, y, z))
                                .map_err(|_| "Keccak affine index")
                        };
                        quadratic.push(Quadratic {
                            g,
                            l: theta_wire((x + 1) % 5)?,
                            r: theta_wire((x + 2) % 5)?,
                            k: 0,
                        });
                        for wire in [
                            outputs[at(x, y, z)],
                            real + theta_base + at(x, y, z),
                            real + theta_base + at((x + 2) % 5, y, z),
                        ] {
                            linear.push(Linear {
                                g,
                                l: u32::try_from(wire).map_err(|_| "Keccak residual index")?,
                                k: 0,
                            });
                        }
                        if x == 0 && y == 0 {
                            let constant = (0..active).fold(0u128, |word, lane| {
                                word | (((ROUNDC[(batch * 128 + lane) % 24] >> z) & 1) as u128)
                                    << lane
                            });
                            if constant != 0 {
                                let wire = real + forms.len();
                                forms.push(BitAffineInput {
                                    terms: Vec::new(),
                                    constant,
                                });
                                linear.push(Linear {
                                    g,
                                    l: u32::try_from(wire).map_err(|_| "Keccak iota index")?,
                                    k: 0,
                                });
                            }
                        }
                    }
                }
            }
        }
        let width = real
            .checked_add(forms.len())
            .filter(|n| *n <= u32::MAX as usize)
            .ok_or("round-packed Keccak input width")?;
        let outputs = round_batches * 1600;
        let f = F::new();
        let raw = RawCircuitBuilder {
            ninput: width,
            npublic_input: 0,
            noutput: outputs,
            logv: ceil_log2(outputs),
            constants: vec![f.one()],
            layers: vec![Layer::new(
                width,
                Stream::<Quadratic>::from_terms(quadratic),
                Stream::<Linear>::from_terms(linear),
                Stream::default(),
            )],
        }
        .build();
        let mut source = Sha256::new();
        source.update(b"SHAKE128-256/round-packed-bit-layout/v1");
        source.update((private as u64).to_le_bytes());
        for &(word, lane) in &placements {
            source.update((word as u64).to_le_bytes());
            source.update([lane]);
        }
        let program = Program::new_with_bit_views(
            Circuit::from_raw(&f, raw),
            real,
            maps,
            forms,
            source.finalize().into(),
        )?;
        Ok(Self {
            program,
            placements,
            round_batches,
            start_batches,
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
            self.round_batches,
            self.start_batches,
            self.links.len(),
        ] {
            out.extend((n as u64).to_le_bytes());
        }
        for (start, end) in &self.links {
            for &bit in start.iter().chain(end) {
                out.extend((bit as u64).to_le_bytes());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests;

cfg_prover! {mod prover;}
