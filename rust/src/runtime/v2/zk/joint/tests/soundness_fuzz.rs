// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Structural soundness fuzz of the frontend stack (the re-audit's probe P2).
//!
//! Random lists of random layered circuits (quadratic, linear and constant
//! terms, quadratic and linear assertions, entering outputs at every depth,
//! zero-layer components) over one shared input array. A reference evaluator
//! written from the sumcheck DESIGN.md decides whether a witness satisfies
//! the list. Honest witnesses must verify. Then single inputs are changed;
//! whenever the reference says the statement became false, the crate's own
//! prover runs with its self-checks disabled (`transcript::cheat`) and the
//! verifier must reject. The cases are drawn from fixed seeds.
use super::*;
use crate::runtime::{
    algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    },
    v2::transcript::{cheat::cheating, Unverified},
};

pub(crate) struct Sm(pub(crate) u64);
impl Sm {
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

#[derive(Clone)]
struct GenLayer {
    nw: usize,
    quad: Vec<Quadratic>,
    lin: Vec<Linear>,
    cst: Vec<Constant>,
}
pub(crate) struct GenCircuit<E> {
    pub(crate) ninput: usize,
    pub(crate) npublic: usize,
    pub(crate) noutput: usize,
    pub(crate) constants: Vec<E>,
    /// Outputs toward inputs, as in `RawCircuit::layers`.
    layers: Vec<GenLayer>,
}

/// One layer's outputs and whether every assertion holds, by the DESIGN.md
/// semantics: a record whose coefficient is zero asserts its factor(s).
fn layer_eval<F: AlgebraicField>(
    f: &F,
    constants: &[F::E],
    l: &GenLayer,
    w: &[F::E],
    nout: usize,
) -> (Vec<F::E>, bool) {
    let mut out = vec![f.zero(); nout];
    let mut ok = true;
    for q in &l.quad {
        let prod = f.mulf(&w[q.l as usize], &w[q.r as usize]);
        if f.is_zero(&constants[q.k as usize]) {
            ok &= f.is_zero(&prod);
        } else {
            f.add(
                &mut out[q.g as usize],
                &f.mulf(&constants[q.k as usize], &prod),
            );
        }
    }
    for t in &l.lin {
        if f.is_zero(&constants[t.k as usize]) {
            ok &= f.is_zero(&w[t.l as usize]);
        } else {
            f.add(
                &mut out[t.g as usize],
                &f.mulf(&constants[t.k as usize], &w[t.l as usize]),
            );
        }
    }
    for c in &l.cst {
        f.add(&mut out[c.g as usize], &constants[c.k as usize]);
    }
    (out, ok)
}

/// Reference satisfaction of one circuit on the shared inputs.
pub(crate) fn satisfied<F: AlgebraicField>(f: &F, c: &GenCircuit<F::E>, inputs: &[F::E]) -> bool {
    let mut w = inputs[..c.ninput].to_vec();
    let mut ok = true;
    for j in (0..c.layers.len()).rev() {
        let nout = if j == 0 {
            c.noutput
        } else {
            c.layers[j - 1].nw
        };
        let (out, good) = layer_eval(f, &c.constants, &c.layers[j], &w, nout);
        ok &= good;
        w = out;
    }
    ok && w.iter().all(|x| f.is_zero(x))
}

/// A random circuit of `depth` layers that `inputs[..ninput]` satisfies.
pub(crate) fn generate<F: AlgebraicField>(
    f: &F,
    rng: &mut Sm,
    inputs: &[F::E],
    ninput: usize,
    npublic: usize,
    depth: usize,
    general: &[F::E],
) -> GenCircuit<F::E> {
    let mut constants = vec![f.zero(), f.one(), f.mone()];
    constants.extend_from_slice(general);
    let nk = constants.len();
    let mut w = inputs[..ninput].to_vec();
    let mut up = Vec::new();
    for level in 0..depth {
        let top = level + 1 == depth;
        let nw = w.len();
        let nout = 1 + rng.below(5);
        let mut layer = GenLayer {
            nw,
            quad: Vec::new(),
            lin: Vec::new(),
            cst: Vec::new(),
        };
        for _ in 0..rng.below(2 * nout + 2) {
            layer.quad.push(Quadratic {
                g: rng.below(nout) as u32,
                l: rng.below(nw) as u32,
                r: rng.below(nw) as u32,
                k: (1 + rng.below(nk - 1)) as u32,
            });
        }
        for _ in 0..rng.below(nout + 2) {
            layer.lin.push(Linear {
                g: rng.below(nout) as u32,
                l: rng.below(nw) as u32,
                k: (1 + rng.below(nk - 1)) as u32,
            });
        }
        for _ in 0..rng.below(3) {
            layer.cst.push(Constant {
                g: rng.below(nout) as u32,
                k: (1 + rng.below(nk - 1)) as u32,
            });
        }
        // Assertions on wires that are zero in the satisfying witness.
        let zeros: Vec<usize> = (0..nw).filter(|&i| f.is_zero(&w[i])).collect();
        if !zeros.is_empty() {
            for _ in 0..rng.below(4) {
                let z = zeros[rng.below(zeros.len())] as u32;
                let other = rng.below(nw) as u32;
                let g = rng.below(nout) as u32;
                match rng.below(3) {
                    0 => layer.quad.push(Quadratic {
                        g,
                        l: z,
                        r: other,
                        k: 0,
                    }),
                    1 => layer.quad.push(Quadratic {
                        g,
                        l: other,
                        r: z,
                        k: 0,
                    }),
                    _ => layer.lin.push(Linear { g, l: z, k: 0 }),
                }
            }
        }
        // Shuffle so assertion records interleave with ordinary ones.
        for i in (1..layer.quad.len()).rev() {
            layer.quad.swap(i, rng.below(i + 1));
        }
        for i in (1..layer.lin.len()).rev() {
            layer.lin.swap(i, rng.below(i + 1));
        }
        let (mut out, ok) = layer_eval(f, &constants, &layer, &w, nout);
        assert!(ok);
        // Cancel every top output, and some lower wires for later assertions.
        for (g, o) in out.iter_mut().enumerate() {
            if (top || rng.below(3) == 0) && !f.is_zero(o) {
                constants.push(f.neg(o));
                layer.cst.push(Constant {
                    g: g as u32,
                    k: (constants.len() - 1) as u32,
                });
                *o = f.zero();
            }
        }
        up.push(layer);
        w = out;
    }
    up.reverse();
    GenCircuit {
        ninput,
        npublic,
        noutput: w.len(),
        constants,
        layers: up,
    }
}

pub(crate) fn build<F: SerializableField + AlgebraicField>(
    f: &F,
    c: &GenCircuit<F::E>,
) -> Circuit<F> {
    let layers = c
        .layers
        .iter()
        .map(|l| {
            Layer::new(
                l.nw,
                Stream::<Quadratic>::from_terms(l.quad.iter().copied()),
                Stream::<Linear>::from_terms(l.lin.iter().copied()),
                Stream::<Constant>::from_terms(l.cst.iter().copied()),
            )
        })
        .collect();
    let raw = RawCircuitBuilder {
        ninput: c.ninput,
        npublic_input: c.npublic,
        noutput: c.noutput,
        logv: crate::util::ceil_log2(c.noutput.max(1)),
        constants: c.constants.clone(),
        layers,
    }
    .build();
    Circuit::from_raw(f, raw)
}

struct Outcome {
    honest: usize,
    falsified: usize,
    accepted_false: Vec<String>,
    /// False statements the cheating prover could not prove at all, so that
    /// the verifier never saw them.
    unproved: Vec<String>,
}

#[allow(clippy::too_many_arguments)]
fn run<F, D>(
    f: &F,
    domain: &D,
    seed: u64,
    cases: usize,
    binary: bool,
    to_input: impl Fn(&F::E) -> CircuitInput<F>,
    general: &[F::E],
    change: impl Fn(&F::E, u64) -> F::E,
) -> Outcome
where
    F: ZkField + PackingField,
    D: EvaluationDomain<F>,
    F::E: PartialEq,
    CircuitInput<F>: Clone,
{
    let config = PolygeroConfig {
        k: 64,
        s: 2,
        n: 256,
        t: 8,
    };
    let mut rng = Sm(seed);
    let mut outcome = Outcome {
        honest: 0,
        falsified: 0,
        accepted_false: Vec::new(),
        unproved: Vec::new(),
    };
    for case in 0..cases {
        let ncircuits = 1 + rng.below(3);
        let npublic = rng.below(3);
        let depths: Vec<usize> = (0..ncircuits)
            .map(|_| {
                if rng.below(6) == 0 {
                    0
                } else {
                    1 + rng.below(3)
                }
            })
            .collect();
        let widths: Vec<usize> = (0..ncircuits)
            .map(|_| npublic.max(1) + rng.below(9))
            .collect();
        let n = *widths.iter().max().unwrap();
        // Inputs: zero on every zero-layer component's prefix; a few other zeros.
        let zero_prefix = depths
            .iter()
            .zip(&widths)
            .filter(|(d, _)| **d == 0)
            .map(|(_, w)| *w)
            .max()
            .unwrap_or(0);
        let inputs: Vec<F::E> = (0..n)
            .map(|i| {
                if i < zero_prefix || rng.below(4) == 0 {
                    f.zero()
                } else if binary {
                    f.one()
                } else {
                    change(&f.zero(), 1 + rng.next() % 1000)
                }
            })
            .collect();
        let gens: Vec<GenCircuit<F::E>> = (0..ncircuits)
            .map(|c| generate(f, &mut rng, &inputs, widths[c], npublic, depths[c], general))
            .collect();
        assert!(gens.iter().all(|g| satisfied(f, g, &inputs)));
        let circuits: Vec<Circuit<F>> = gens.iter().map(|g| build(f, g)).collect();
        let components: Vec<&Circuit<F>> = circuits.iter().collect();
        let p = match CircuitParticipant::new(&components, 0, config, domain) {
            Ok(p) => p,
            Err(e) => panic!("case {case}: participant: {e}"),
        };
        let label = format!("re-checks/fuzz/{seed}/{case}");
        let attempt = |values: &[F::E], cheat: bool, prng: u64| -> Result<(), String> {
            let public: Vec<CircuitInput<F>> = values[..npublic].iter().map(&to_input).collect();
            let private: Vec<CircuitInput<F>> = values[npublic..].iter().map(&to_input).collect();
            let mut prover_rng = DeterministicRng::new(prng);
            let mut prove_all = || -> Result<_, String> {
                let (state, w) = p.prepare(private.clone(), &mut prover_rng)?;
                let param = JointParam::new((p.participant(domain)?, ()))?;
                let t = Transcript::for_test(label.as_bytes());
                let (mut joint, root, responses) = param.commit((w, ()), t, &mut prover_rng)?;
                let part = FrontendPart::new(&p, &components, &public)?;
                let (proof, statement) =
                    zk::prove(&mut joint.bound(&part), state, &VirtualInputs::none())?;
                let (opening, _) = joint.finish(&param, (statement, ()))?;
                Ok((param, root, responses, proof, opening))
            };
            let (param, root, responses, proof, opening) = if cheat {
                cheating(&mut prove_all)
            } else {
                prove_all()
            }
            .map_err(|e| format!("prover: {e}"))?;
            let t = Transcript::for_test(label.as_bytes());
            let mut v = param.receive(&root, responses, t);
            let part = FrontendPart::new(&p, &components, &public)?;
            let statement = zk::reduce(&mut v.bound(&part), &proof, &VirtualInputs::none())?;
            v.finish((statement, ()), Unverified::unsealed_for_test(&opening))
                .map(|_| ())
        };
        if let Err(e) = attempt(&inputs, false, 1000 + case as u64) {
            panic!("case {case}: honest proof rejected: {e} (depths {depths:?}, widths {widths:?}, npublic {npublic})");
        }
        outcome.honest += 1;
        // Change one input at a time.
        for i in 0..n {
            let mut bad = inputs.clone();
            bad[i] = if binary {
                if f.is_zero(&bad[i]) {
                    f.one()
                } else {
                    f.zero()
                }
            } else {
                change(&bad[i], 1 + rng.next() % 5)
            };
            if gens.iter().all(|g| satisfied(f, g, &bad)) {
                continue;
            }
            outcome.falsified += 1;
            match attempt(&bad, true, 5000 + (case * 64 + i) as u64) {
                Ok(()) => outcome.accepted_false.push(format!(
                    "seed {seed} case {case} input {i}: depths {depths:?} widths {widths:?} npublic {npublic}"
                )),
                Err(e) if e.starts_with("prover:") => outcome.unproved.push(format!("case {case} input {i}: {e}")),
                Err(_) => {}
            }
        }
    }
    outcome
}

/// Cases per field: enough to reach every generator branch (zero-layer
/// components, assertions at every depth, one to three circuits) in a
/// normal test run; the re-audit ran 150.
const CASES: usize = 32;

/// Random honest statements verify, and every single-input change that the
/// reference finds false is rejected, even from a prover that ignores its
/// own checks, in GF(2^128) and in P-256.
#[test]
fn cheating_provers_of_false_random_statements_are_rejected() {
    let gf = Gf2_128Field::new();
    let domain = BinaryInterpolatorFactory::full_field(&gf);
    use crate::core::algebra::SupportsU128Conversions;
    let general = [
        gf.u128_to_element(0x1234_5678_9abc_def0_0fed_cba9_8765_4321),
        gf.u128_to_element(7),
    ];
    let binary = run(
        &gf,
        &domain,
        11,
        CASES,
        true,
        |x| !gf.is_zero(x),
        &general,
        |x, _| *x,
    );
    let p = P256Field::new();
    let p2 = Fp2Field::new(&p);
    let pd = QuadraticExtensionFftInterpolatorFactory::new(&p, &p2, p2.omega(), p2.omega_order());
    let prime_general = [p.u64_to_element(0xdead_beef_1234), p.u64_to_element(3)];
    let prime = run(
        &p,
        &pd,
        12,
        CASES,
        false,
        |x| *x,
        &prime_general,
        |x, d| p.addf(x, &p.u64_to_element(d)),
    );
    for outcome in [&binary, &prime] {
        assert_eq!(outcome.honest, CASES);
        assert!(outcome.falsified > 0, "no false statement was tried");
        assert!(
            outcome.unproved.is_empty(),
            "not proved: {:?}",
            outcome.unproved
        );
        assert!(
            outcome.accepted_false.is_empty(),
            "false statements accepted: {:?}",
            outcome.accepted_false
        );
    }
}
