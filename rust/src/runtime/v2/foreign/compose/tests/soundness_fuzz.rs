// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Structural soundness fuzz of the composition driver (the re-audit's probe
//! P3).
//!
//! A random binary host circuit and a random P-256 split circuit share random
//! bit groups (widths 1 to 130) of the host's private inputs: the split
//! circuit's foreign private inputs. A reference decides whether the host
//! circuit, the split circuit and every link (foreign value = integer of its
//! bits) hold. Honest instances must verify. Then one host bit or one split
//! input is changed; whenever the reference says the composed statement
//! became false, the crate's own prover runs with its self-checks off
//! (`transcript::cheat`), in two ways, and the verifier must reject:
//!
//! - the split message and the adapter follow the split frontend's own values;
//! - they follow the host's committed bits (`cheat::cheating_from_host_bits`).
//!
//! The cases are drawn from a fixed seed.
use super::*;
use crate::runtime::v2::{
    transcript::cheat,
    zk::joint::tests::soundness_fuzz::{build, generate, satisfied, GenCircuit, Sm},
};

/// The adapter mode of the fuzz: R's 256 bits and up to 130-bit groups.
type FuzzMode = P256Mode<10>;

/// Cases: enough to cover groups of every width class, zero-layer hosts and
/// both cheats on host bits and split inputs in a normal test run (about a
/// hundred false statements per eight cases); the re-audit ran 600.
const CASES: usize = 32;

/// The integer of `bits`, least significant first, in P-256.
fn group_value(p: &P256Field, bits: &[bool]) -> <P256Field as crate::core::algebra::BareField>::E {
    let mut v = p.zero();
    for &b in bits.iter().rev() {
        v = p.addf(&v, &v);
        if b {
            v = p.addf(&v, &p.one());
        }
    }
    v
}

/// How a composed statement is proved: honestly, or with the prover's
/// self-checks off and the foreign values taken from the split frontend or
/// from the host's bits.
#[derive(Clone, Copy, Debug)]
enum Prover {
    Honest,
    Cheating,
    FromHostBits,
}

/// Random honest compositions verify, and every single host bit or split
/// input change that the reference finds false is rejected by the verifier,
/// even from a prover that ignores its own checks and from one that links
/// the split to the host's bits.
#[test]
fn cheating_provers_of_false_random_compositions_are_rejected() {
    let gf2 = Gf2_128Field::new();
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let host_domain = BinaryInterpolatorFactory::full_field(&gf2);
    let split_domain =
        QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    use crate::core::algebra::SupportsU128Conversions;
    let host_general = [
        gf2.u128_to_element(0xfeed_face_cafe_beef),
        gf2.u128_to_element(5),
    ];
    let split_general = [p.u64_to_element(0x1234_5678_9abc), p.u64_to_element(7)];
    let mut rng = Sm(2026);
    let (mut falsified, mut accepted, mut unproved) = (0usize, Vec::new(), Vec::new());
    for case in 0..CASES {
        // Host inputs: bits.
        let hpub = rng.below(3);
        let hpriv = 4 + rng.below(160);
        let hn = hpub + hpriv;
        let hdepth = if rng.below(8) == 0 {
            0
        } else {
            1 + rng.below(3)
        };
        let host_bits: Vec<bool> = (0..hn).map(|_| hdepth != 0 && rng.below(2) == 1).collect();
        let host_inputs: Vec<_> = host_bits
            .iter()
            .map(|&b| if b { gf2.one() } else { gf2.zero() })
            .collect();
        let hgen = generate(
            &gf2,
            &mut rng,
            &host_inputs,
            hn,
            hpub,
            hdepth,
            &host_general,
        );
        let host = build(&gf2, &hgen);
        // Split inputs: some private inputs are foreign groups of host bits.
        let spub = rng.below(3);
        let spriv = 1 + rng.below(6);
        let sn = spub + spriv;
        let sdepth = 1 + rng.below(3);
        let nforeign = 1 + rng.below(spriv);
        let mut foreign: Vec<(usize, Group)> = Vec::new();
        let mut taken = vec![false; spriv];
        for _ in 0..nforeign {
            let j = rng.below(spriv);
            if taken[j] {
                continue;
            }
            taken[j] = true;
            let width = match rng.below(6) {
                0 => 1,
                1 => 2,
                2 => 64,
                3 => 65,
                4 => 130,
                _ => 1 + rng.below(40),
            }
            .min(hpriv);
            let start = hpub + rng.below(hpriv - width + 1);
            foreign.push((j, Group::new(start, width).unwrap()));
        }
        foreign.sort_by_key(|(j, _)| *j);
        let mut split_inputs: Vec<_> = (0..sn)
            .map(|_| p.u64_to_element(rng.next() % 1000))
            .collect();
        for (j, g) in &foreign {
            split_inputs[spub + j] = group_value(&p, &host_bits[g.start()..g.end()]);
        }
        let sgen = generate(
            &p,
            &mut rng,
            &split_inputs,
            sn,
            spub,
            sdepth,
            &split_general,
        );
        let split = build(&p, &sgen);
        let storage = StorageMap::new(value_count(&split).unwrap(), &foreign).unwrap();
        let c = Composition::<P256Field, _, _, FuzzMode>::new(
            &host,
            &split,
            storage,
            CONFIG,
            (&host_domain, &split_domain),
        )
        .unwrap_or_else(|e| panic!("case {case}: composition: {e}"));
        let label = format!("compose-fuzz/{case}");
        // The reference: both circuits and every link.
        let holds = |h: &GenCircuit<_>, s: &GenCircuit<_>, hb: &[bool], sv: &[_]| {
            let hi: Vec<_> = hb
                .iter()
                .map(|&b| if b { gf2.one() } else { gf2.zero() })
                .collect();
            satisfied(&gf2, h, &hi)
                && satisfied(&p, s, sv)
                && foreign
                    .iter()
                    .all(|(j, g)| sv[spub + j] == group_value(&p, &hb[g.start()..g.end()]))
        };
        assert!(holds(&hgen, &sgen, &host_bits, &split_inputs));
        // Prove with `prover`, then verify: the prover's error or the
        // verifier's verdict.
        let attempt = |hb: &[bool], sv: &[_], prover: Prover, seed: u64| -> Result<bool, String> {
            let statement = c
                .statement(
                    ZkStatement {
                        context: label.as_bytes(),
                    },
                    &hb[..hpub],
                    &sv[..spub],
                )
                .map_err(|e| format!("statement: {e}"))?;
            let prove = || {
                ComposedStatement::prove(
                    Opened::new(&statement),
                    hb[hpub..].to_vec(),
                    sv[spub..].to_vec(),
                    &mut DeterministicRng::new(seed),
                )
            };
            let (proof, _) = match prover {
                Prover::Honest => prove(),
                Prover::Cheating => cheat::cheating(prove),
                Prover::FromHostBits => cheat::cheating_from_host_bits(prove),
            }
            .map_err(|e| format!("prover: {e}"))?;
            Ok(ComposedStatement::reduce_and_authenticate(Opened::new(&statement), &proof).is_ok())
        };
        let honest = attempt(&host_bits, &split_inputs, Prover::Honest, 100 + case as u64);
        assert_eq!(
            honest,
            Ok(true),
            "case {case}: honest composition (hdepth {hdepth} sdepth {sdepth} foreign {foreign:?})"
        );
        let mut record = |what: String, r: Result<bool, String>| match r {
            Ok(true) => accepted.push(what),
            Ok(false) => {}
            Err(e) => unproved.push(format!("{what}: {e}")),
        };
        // One host bit changed: a sample of positions, and a bit of every group.
        let mut positions: Vec<usize> = (0..12).map(|_| rng.below(hn)).collect();
        for (_, g) in &foreign {
            positions.push(g.start() + rng.below(g.width()));
            positions.push(g.end() - 1);
        }
        for i in positions {
            let mut hb = host_bits.clone();
            hb[i] = !hb[i];
            if holds(&hgen, &sgen, &hb, &split_inputs) {
                continue;
            }
            falsified += 1;
            for prover in [Prover::Cheating, Prover::FromHostBits] {
                let seed = 7000 + (case * 1000 + i) as u64;
                record(
                    format!("case {case} host bit {i} {prover:?} foreign {foreign:?}"),
                    attempt(&hb, &split_inputs, prover, seed),
                );
            }
        }
        // One split input changed.
        for j in 0..sn {
            let mut sv = split_inputs.clone();
            sv[j] = p.addf(&sv[j], &p.u64_to_element(1 + rng.next() % 3));
            if holds(&hgen, &sgen, &host_bits, &sv) {
                continue;
            }
            falsified += 1;
            for prover in [Prover::Cheating, Prover::FromHostBits] {
                let seed = 9000 + (case * 1000 + j) as u64;
                record(
                    format!("case {case} split input {j} {prover:?} foreign {foreign:?}"),
                    attempt(&host_bits, &sv, prover, seed),
                );
            }
        }
    }
    assert!(falsified > 0, "no false statement was tried");
    assert!(unproved.is_empty(), "not proved: {unproved:?}");
    assert!(
        accepted.is_empty(),
        "false statements accepted: {accepted:?}"
    );
}
