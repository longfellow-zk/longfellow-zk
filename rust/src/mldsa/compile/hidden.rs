// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compile the private issuer expansion and native NTT relation to archives.
use crate::{
    compile::{
        algebra::{fp24_ext6::CompileFp24Ext6 as AF, gf2_128::Gf2_128Field as BF},
        compiler::{compile_v2, compile_v2_shared_inputs, segment_circuit_v2},
        logic::{Logic, LogicIO, K_FIRST_WIRE_POSITION},
    },
    core::proto::v2::CircuitWriter,
    mldsa::{
        compile::{
            circuits::{self, hidden},
            native_inputs, native_words,
        },
        proto::{self, BinaryKeccak, HiddenArchive, MlDsaParams, Source, N},
    },
};
pub fn compile_hidden<P: MlDsaParams>(keccak: BinaryKeccak) -> Result<HiddenArchive, String> {
    keccak.validate();
    let af = AF::new();
    let (native_unsegmented, _, _) = compile_v2(&af, |l| hidden::build::<P>(l, 4));
    let native = segment_circuit_v2(&af, native_unsegmented);
    if native.raw.ninput != native_inputs::<P>() {
        return Err("hidden native layout".into());
    }
    let arithmetic = CircuitWriter::new(&af).to_bytes(&native);
    let shared_widths = proto::shared_widths::<P>();
    let shared_count = shared_widths.len();
    let mut widths = shared_widths;
    widths.extend(vec![23; native_words::<P>()]);
    let sources: Vec<_> = widths
        .into_iter()
        .enumerate()
        .map(|(value, width)| Source {
            value,
            coordinate: 0,
            width,
        })
        .collect();
    let mut positions = vec![];
    let mut links = vec![];
    let mut base_private = 0;
    let mut key_start = 0;
    let f = BF::new();
    let (binary_unsegmented, _, _) = compile_v2_shared_inputs(&f, |l| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let gamma: Vec<_> = (0..2).map(|_| l.next(&mut pos)).collect();
        let public = pos;
        let witness = circuits::allocate_private::<_, P>(&l, &mut pos, keccak);
        // Shared::input allocates z, h, raw, auxiliary, hinted, positive and
        // negative in this order. Select exactly the native participant's bits.
        let mut at = public - 1;
        positions.extend(at..at + P::L * N * P::Z_BITS);
        at += P::L * N * P::Z_BITS + P::K * N;
        positions.extend(at..at + P::K * N * P::R1_BITS);
        at += P::K * N * P::R1_BITS;
        for _ in 0..P::K * N {
            positions.extend(at..at + P::r0_bits());
            at += P::r0_bits() + 1;
        }
        at += P::K * N * P::R1_BITS;
        positions.extend(at..at + 2 * N);
        links.extend(witness.permutation_links(&l));
        let mut checks = circuits::signature_assertions::<_, P>(&l, witness, keccak);
        key_start = pos - public;
        let key_begin = pos;
        let (key, mut key_checks, key_links) =
            hidden::allocate_issuer_key::<_, P>(&l, &mut pos, &gamma, keccak);
        let mut external = Vec::new();
        external.push(key_begin..key_begin + key.len());
        positions.extend(key_begin - 1..key_begin - 1 + key.len());
        checks.append(&mut key_checks);
        links.extend(key_links);
        for (a, b) in &links {
            for v in [a, b] {
                external.push(v[0] + 1..v[v.len() - 1] + 2);
            }
        }
        base_private = pos - public;
        (l.assert_all("hidden_mldsa", &checks), public, external)
    });
    let binary = segment_circuit_v2(&f, binary_unsegmented);
    let mut next = binary.raw.ninput;
    for source in &sources[shared_count..] {
        positions.extend(next..next + source.width);
        next += source.width;
    }
    if positions.len() != sources.iter().map(|s| s.width).sum::<usize>() {
        return Err("hidden binary source positions".into());
    }
    Ok(HiddenArchive {
        binary: CircuitWriter::new(&f).to_bytes(&binary),
        arithmetic,
        keccak,
        sources,
        positions,
        links,
        base_private,
        key_start,
    })
}
