// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{circuit::compile_base, *};
use crate::{
    circuits::sha256::Given,
    compile::algebra::gf2_128::Gf2_128Field as CF,
    core::proto::v2::{Circuit, CircuitReader, CircuitWriter},
    runtime::{
        algebra::gf2_128::{Gf2_128 as E, Gf2_128Field as F},
        random::{DeterministicRng, RandomEngine},
    },
};
fn runtime(compiled: &Circuit<CF>) -> Circuit<F> {
    let bytes = CircuitWriter::new(&CF::new()).to_bytes(compiled);
    let (c, tail) = CircuitReader::new(&F::new()).from_bytes(&bytes).unwrap();
    assert!(tail.is_empty());
    c
}
fn evaluate(c: &Circuit<F>, mut input: Vec<E>) -> Result<Vec<E>, String> {
    for (i, l) in c.raw.layers.iter().enumerate().rev() {
        let n = if i == 0 {
            c.raw.noutput
        } else {
            c.raw.layers[i - 1].nw
        };
        let mut out = vec![E::from(0); n];
        l.quadratic.try_for_each(|v| {
            let x = E::from(input[v.l as usize].to_u128() & input[v.r as usize].to_u128());
            if c.raw.constants[v.k as usize] == E::from(0) {
                if x != E::from(0) {
                    return Err(format!("quadratic assertion layer {i}"));
                }
            } else {
                out[v.g as usize].xor_in_place(&x);
            }
            Ok(())
        })?;
        l.linear.try_for_each(|v| {
            let x = input[v.l as usize];
            if c.raw.constants[v.k as usize] == E::from(0) {
                if x != E::from(0) {
                    return Err(format!("linear assertion layer {i}"));
                }
            } else {
                out[v.g as usize].xor_in_place(&x);
            }
            Ok(())
        })?;
        l.constant.for_each(|v| {
            if c.raw.constants[v.k as usize] != E::from(0) {
                out[v.g as usize].xor_in_place(&E::from(u128::MAX));
            }
        });
        input = out;
    }
    Ok(input)
}
#[test]
fn all_packed_sha_views_agree_with_native_traces() {
    let mut rng = DeterministicRng::new(123);
    let given: Vec<_> = (0..128)
        .map(|_| Given {
            input_block: std::array::from_fn(|_| rng.u128() as u32),
            h0: std::array::from_fn(|_| rng.u128() as u32),
        })
        .collect();
    let original = pack_instances(&given);
    let base = runtime(&compile_base().unwrap());
    let result = evaluate(&base, original.clone()).unwrap();
    assert!(
        result.iter().all(|x| *x == E::from(0)),
        "base residual {:?}",
        result.iter().position(|x| *x != E::from(0))
    );
    for index in [0, 24 * 32, INPUT_BITS - 1] {
        let mut bad = original.clone();
        bad[index].xor_in_place(&E::from(1));
        assert!(
            match evaluate(&base, bad) {
                Ok(residuals) => residuals.iter().any(|x| *x != E::from(0)),
                Err(_) => true,
            },
            "unchecked SHA witness bit {index}"
        );
    }
    let flat = flat::compile(flat::Policy::Products).unwrap();
    assert_eq!(
        flat.circuit.raw.ninput,
        INPUT_BITS + flat.additional_bits_per_lane()
    );
    assert_eq!(flat.circuit.raw.layers.len(), 1);
    let words: Vec<E> = flat
        .advice()
        .evaluate(&original.iter().map(|x| x.to_u128()).collect::<Vec<_>>())
        .unwrap()
        .into_iter()
        .map(E::from)
        .collect();
    let flat_result = evaluate(&runtime(&flat.circuit), words.clone()).unwrap();
    assert!(
        flat_result.iter().all(|x| *x == E::from(0)),
        "flat residual {:?}",
        flat_result.iter().position(|x| *x != E::from(0))
    );
    let (c, forms) = flat.factored();
    let mut expanded = words.clone();
    for a in forms {
        let mut x = if a.constant { u128::MAX } else { 0 };
        for i in a.vars {
            x ^= words[i].to_u128();
        }
        expanded.push(E::from(x));
    }
    let factored_result = evaluate(&runtime(&c), expanded).unwrap();
    assert!(
        factored_result.iter().all(|x| *x == E::from(0)),
        "factored residual {:?}",
        factored_result.iter().position(|x| *x != E::from(0))
    );
}
