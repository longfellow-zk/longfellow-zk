// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Product equations over the application's common Boolean input array.
//!
//! Only coefficients depend on challenges. Local intermediate wires hold two
//! data products and two quotient products; the input layer reads the common
//! source array directly. No leaves or intermediate products are committed.
use super::Plan;
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::v2::{self, Circuit, Constant, Layer, Linear, Quadratic, RawCircuit, Stream},
    },
    runtime::algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
};

pub(crate) fn program(
    plan: &Plan,
    sources: &[usize],
    npublic: usize,
    ninput: usize,
    public: &[E],
) -> Result<RawCircuit<F>, String> {
    let private = ninput.checked_sub(npublic).ok_or("adapter public prefix")?;
    if sources.len() != plan.bits
        || public.len() != plan.public_count()
        || private < plan.advice_bits()
        || sources
            .iter()
            .any(|&i| i < npublic || i >= ninput - plan.advice_bits())
        || ninput > u32::MAX as usize
        || public[plan.powers..plan.powers + plan.advice_bits()]
            .iter()
            .any(|x| x.to_u128() > 1)
    {
        return Err("adapter tree input layout".into());
    }
    let f = F::new();
    let mut constants = vec![f.one()];
    let mut put = |value: E| {
        let k = constants.len() as u32;
        constants.push(value);
        k
    };
    let mut linear = Vec::new();
    let mut constant = Vec::new();
    let q = plan.quotient_coefficients(&f);
    let width = plan.bits + plan.quotient_bits;
    for tree in 0..2 {
        for i in 0..width {
            let g = (tree * width + i) as u32;
            let (wire, power, base) = if i < plan.bits {
                (
                    sources[i],
                    f.addf(&public[tree * plan.bits + i], &f.one()),
                    f.one(),
                )
            } else {
                let j = i - plan.bits;
                let k = tree * plan.quotient_bits + j;
                let power = f.addf(&q[j], &f.one());
                let base = if public[plan.powers + k].to_u128() == 1 {
                    power
                } else {
                    f.one()
                };
                (ninput - plan.advice_bits() + k, power, base)
            };
            if f.is_zero(&power) {
                return Err("adapter leaf power must be nonzero".into());
            }
            // Write 1+b*(power-1) as 1+power*b+b. Both coefficients
            // remain nonzero even when power=1: zero linear coefficients
            // encode assertions in LFC3. This keeps the topology fixed.
            linear.push(Linear {
                g,
                l: wire as u32,
                k: put(power),
            });
            linear.push(Linear {
                g,
                l: wire as u32,
                k: 0,
            });
            constant.push(Constant { g, k: put(base) });
        }
    }
    let mut layers = vec![Layer::with_assertions(
        ninput,
        Stream::default(),
        Stream::<Linear>::from_terms(linear),
        Stream::<Constant>::from_terms(constant),
        |_| false,
    )];
    let (mut data, mut advice) = (plan.bits, plan.quotient_bits);
    while data > 1 || advice > 1 {
        let (nd, nq) = (data.div_ceil(2), advice.div_ceil(2));
        let mut quadratic = Vec::new();
        let mut linear = Vec::new();
        for tree in 0..2 {
            let src = tree * (data + advice);
            let dst = tree * (nd + nq);
            for (n, count, src, dst) in [(data, nd, src, dst), (advice, nq, src + data, dst + nd)] {
                for i in 0..count {
                    if 2 * i + 1 < n {
                        quadratic.push(Quadratic {
                            g: (dst + i) as u32,
                            l: (src + 2 * i) as u32,
                            r: (src + 2 * i + 1) as u32,
                            k: 0,
                        });
                    } else {
                        linear.push(Linear {
                            g: (dst + i) as u32,
                            l: (src + 2 * i) as u32,
                            k: 0,
                        });
                    }
                }
            }
        }
        layers.push(Layer::with_assertions(
            2 * (data + advice),
            Stream::<Quadratic>::from_terms(quadratic),
            Stream::<Linear>::from_terms(linear),
            Stream::default(),
            |_| false,
        ));
        data = nd;
        advice = nq;
    }
    let mut targets = Vec::new();
    for tree in 0..2 {
        let target = public[public.len() - 2 + tree];
        if f.is_zero(&target) {
            return Err("adapter target must be nonzero".into());
        }
        targets.push(Constant {
            g: tree as u32,
            k: put(target),
        });
    }
    layers.push(Layer::with_assertions(
        4,
        Stream::<Quadratic>::from_terms((0..2).map(|g| Quadratic {
            g,
            l: 2 * g,
            r: 2 * g + 1,
            k: 0,
        })),
        Stream::default(),
        Stream::<Constant>::from_terms(targets),
        |_| false,
    ));
    layers.reverse();
    Ok(RawCircuit {
        ninput,
        npublic_input: npublic,
        noutput: 2,
        logv: 1,
        constants,
        layers,
    })
}

/// The template has the same topology and geometry as every challenge instance.
pub(crate) fn template(
    plan: &Plan,
    sources: &[usize],
    npublic: usize,
    ninput: usize,
) -> Result<Circuit<F>, String> {
    let f = F::new();
    let mut public = vec![f.zero(); plan.public_count()];
    let n = public.len();
    public[n - 2] = f.one();
    public[n - 1] = f.one();
    let raw = program(plan, sources, npublic, ninput, &public)?;
    Ok(Circuit {
        id: v2::compute_id(&f, &raw),
        raw,
    })
}
