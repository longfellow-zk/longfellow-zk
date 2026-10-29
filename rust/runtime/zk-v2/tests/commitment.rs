// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::{
            circuit::{compute_id, Circuit, RawCircuit},
            Layer, TermDelta,
        },
    },
    runtime::{
        algebra::{
            gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
            subfield_v1::BinarySubfield, PackingField,
        },
        polygero::PolygeroConfig,
        proto::zk_v2::product_constraints,
        random::{DeterministicRng, RandomEngine},
        sumcheck_v2::{self, TranscriptSumcheck},
        zk_v2::ZkContext,
    },
};
#[test]
fn native_rows_and_shared_pad_products_use_the_physical_layout() {
    use crate::runtime::dual_packing::generic;
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let ctx = ZkContext {
        f: &f,
        domain: &domain,
    };
    let raw = RawCircuit {
        ninput: 4,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one(), f.mone()],
        layers: vec![Layer::new_compressed(
            4,
            2,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [1, 2],
                    k_index: 0,
                },
                TermDelta {
                    g: 0,
                    h: [2, 0u32.wrapping_sub(2)],
                    k_index: 1,
                },
            ]],
            vec![0],
        )],
    };
    let c = Circuit {
        id: compute_id(&f, &raw),
        raw,
    };
    let c = crate::core::proto::v2::quadratic_fixture(c, &f);
    let config = PolygeroConfig {
        k: 16,
        s: 2,
        n: 128,
        t: 2,
    };
    let mut rng = DeterministicRng::new(91);
    let mut t = Transcript::new(b"layout");
    let (g, param, backend) =
        crate::runtime::zk_v2::context::prepare_layout(&c, config, f.packing_extension(), &ctx)
            .unwrap();
    let private = vec![f.one(); 3];
    let prepared = backend.prepare_inputs(private).unwrap();
    let (pads, suffix) = sumcheck_v2::sample_pads(&g.sc_geom, &mut rng, &f);
    let state = backend
        .commit(prepared, suffix, param, &c.id, &mut t, &mut rng, &domain)
        .unwrap();
    let mut physical = state.words.clone();
    physical.extend_from_slice(state.masks.cells());
    physical.extend_from_slice(&state.suffix);
    assert_eq!(state.backend.layout.suffix_start, 130);
    for product in product_constraints(state.backend.layout.suffix_start, &g.sc_geom) {
        assert_eq!(
            f.mulf(&physical[product.x], &physical[product.y]),
            physical[product.z]
        );
    }
    t.write_sumcheck_statement(&c, &[f.one()], &f);
    let mut inputs = vec![f.one()];
    inputs.extend(state.private);
    let layers = sumcheck_v2::eval_circuit(inputs, &c, &f).unwrap();
    let (_, constraints) = sumcheck_v2::prove_core(layers, &pads, &c, &mut t, &f);
    let pad_layout = g.sc_geom.pad_layout(state.backend.layout.suffix_start);
    let statement = crate::runtime::zk_v2::constraint_compiler::compile::<2, _>(
        constraints,
        &pad_layout,
        &[f.one()],
        &state.backend.layout,
        &f,
    )
    .unwrap();
    let nrows = statement.b.len();
    let (_, rows) = generic::prove_packed(
        &state.backend.parameters,
        &statement.claim,
        &state.words,
        &state.suffix,
        state.masks,
        &c.id,
        &mut t,
    )
    .unwrap();
    let incomplete = super::super::CommitmentStatement {
        claim: statement.claim.clone(),
        a: Vec::new(),
        b: Vec::new(),
    };
    assert!(state
        .backend
        .authenticate::<2>(incomplete, &rows[1..])
        .is_err());
    let (a, b) = state.backend.authenticate::<2>(statement, &rows).unwrap();
    let eval = |i: usize, w: &[_]| {
        a.iter()
            .filter(|term| term.c == i)
            .fold(b[i], |s, term| f.addf(&s, &f.mulf(&term.k, &w[term.w])))
    };
    for i in 0..b.len() {
        assert_eq!(eval(i, &physical), f.zero());
    }
    let arbitrary = rng.elt_field_slice(physical.len(), &f);
    let l = &state.backend.layout;
    for (i, row) in rows.iter().enumerate() {
        assert_eq!(
            eval(nrows + i, &arbitrary),
            row.residual(
                &arbitrary[..l.packed_words],
                &arbitrary[l.suffix_start..],
                &arbitrary[l.packed_words..l.suffix_start],
                &f
            )
            .unwrap()
        );
    }
}
