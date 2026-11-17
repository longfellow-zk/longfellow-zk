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
#[allow(unused_imports)]
use crate::compile::compiler::tests::source_fixture::compile;
use crate::{
    circuits::ec::{pt2_wires, push_pt2, EcCircuit},
    compile::{
        algebra::{p256::P256Field, secp256r1::Secp256r1, CompileField, CompilePrimeField},
        compiler::dump_stats,
        debug::evaluate::eval_circuit_fc,
        logic::{push_eltw, AssertionScope, Logic, LogicIO, K_FIRST_WIRE_POSITION},
    },
    core::{
        algebra::{
            ec::{add, affine, double, projective, scalar_mul, Curve},
            AlgebraicField, ElementOf, Nat, SerializableField, SupportsNatConversions,
        },
        proto::v2::evaluate::initial_inputs,
    },
    runtime::algebra::RuntimeField,
};

fn test_compile_ec_generic<
    const W: usize,
    FC: CompilePrimeField + SupportsNatConversions<W> + SerializableField,
    FR: RuntimeField + SerializableField,
    CC: Curve<W, F = FC>,
    CR: Curve<W, F = FR>,
>(
    curve_c: &CC,
    fc: &FC,
    curve_r: &CR,
    fr: &FR,
) {
    let (circuit, stats, symbols) = compile(fc, |iologic| {
        let ec_circuit = EcCircuit::new(&iologic, curve_c);

        let mut pos = K_FIRST_WIRE_POSITION;
        let p1 = pt2_wires(&iologic, &mut pos);
        let p2 = pt2_wires(&iologic, &mut pos);
        let p1_double_target = pt2_wires(&iologic, &mut pos);
        let p1_double_zinv = iologic.next(&mut pos);
        let p3_target = pt2_wires(&iologic, &mut pos);
        let p3_zinv = iologic.next(&mut pos);

        let p1_proj = ec_circuit.projective(&p1);
        let p2_proj = ec_circuit.projective(&p2);

        let p1_double_proj = ec_circuit.double(&p1_proj);
        let p3_proj = ec_circuit.add(&p1_proj, &p2_proj);

        let a1 = ec_circuit.is_on_curve(&p1);
        let a2 = ec_circuit.is_on_curve(&p2);
        let a3 = ec_circuit.point_equality(&p1_double_proj, &p1_double_zinv, &p1_double_target);
        let a4 = ec_circuit.point_equality(&p3_proj, &p3_zinv, &p3_target);

        (iologic.assert_all("ec_add_double", &[a1, a2, a3, a4]), 1, 0)
    });

    dump_stats("ec_add_double", &circuit, &stats);

    // Fill concrete values into environment using RuntimeField
    let g_2d_run = curve_r.g();
    let g = projective(curve_r, fr, g_2d_run);

    let g2 = double(curve_r, fr, &g);
    let g2_normalized = affine(fr, &g2);
    let g2_zinv_val = fr.invert(&g2.2);

    // To match circuit execution (where p2 input wire is normalized with Z=1),
    // we must project g2_normalized back to projective coordinates with Z=1.
    let g2_normalized_proj = projective(curve_r, fr, &g2_normalized);
    let g3 = add(curve_r, fr, &g, &g2_normalized_proj);
    let g3_normalized = affine(fr, &g3);
    let g3_zinv_val = fr.invert(&g3.2);

    let mut inputs = initial_inputs(fr);
    push_pt2(g_2d_run, &mut inputs);
    push_pt2(&g2_normalized, &mut inputs);
    push_pt2(&g2_normalized, &mut inputs);
    push_eltw(g2_zinv_val, &mut inputs);
    push_pt2(&g3_normalized, &mut inputs);
    push_eltw(g3_zinv_val, &mut inputs);

    eval_circuit_fc(fc, fr, &circuit, &symbols, &inputs)
        .unwrap()
        .assert_all_passed();
}

#[test]
fn test_compile_ec() {
    let fc = P256Field::new();
    let curve_c = Secp256r1::new(&fc);
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let curve_r = crate::runtime::algebra::secp256r1::Secp256r1::new(&fr);
    test_compile_ec_generic::<4, _, _, _, _>(&curve_c, &fc, &curve_r, &fr);
}

use crate::compile::logic::EvalLogic;

fn test_ec_runtime_arithmetic_robust_generic<
    const W: usize,
    FR: CompileField + SupportsNatConversions<W>,
    C: Curve<W, F = FR>,
>(
    curve: &C,
    fr: &FR,
) {
    // Get curve generator point
    let g_2d = curve.g();
    let g = projective(curve, fr, g_2d);

    // Compute doubling via runtime
    let g2_runtime = double(curve, fr, &g);
    let g2_runtime_normalized = affine(fr, &g2_runtime);

    // Compute doubling via standard affine formulas using CompileField
    let g2_affine = {
        let (x, y) = g_2d;
        let three = fr.addf(&fr.one(), &fr.addf(&fr.one(), &fr.one()));
        let two = fr.addf(&fr.one(), &fr.one());
        let x_sq = fr.mulf(x, x);
        let a_val = curve.a();
        let num = fr.addf(&fr.mulf(&three, &x_sq), a_val);
        let den = fr.mulf(&two, y);
        let lambda = fr.mulf(&num, &fr.invert(&den));
        let two_x = fr.mulf(&two, x);
        let x3 = fr.subf(&fr.mulf(&lambda, &lambda), &two_x);
        let y3 = fr.subf(&fr.mulf(&lambda, &fr.subf(x, &x3)), y);
        (x3, y3)
    };

    // Assert doubling outputs match
    assert_eq!(g2_runtime_normalized.0, g2_affine.0);
    assert_eq!(g2_runtime_normalized.1, g2_affine.1);

    // Compute addition via runtime (G + 2G = 3G)
    let g3_runtime = add(curve, fr, &g, &g2_runtime);
    let g3_runtime_normalized = affine(fr, &g3_runtime);

    // Compute addition via standard affine formulas
    let g3_affine = {
        let (x1, y1) = g_2d;
        let (x2, y2) = &g2_affine;
        let num = fr.subf(y2, y1);
        let den = fr.subf(x2, x1);
        let lambda = fr.mulf(&num, &fr.invert(&den));
        let x3 = fr.subf(&fr.subf(&fr.mulf(&lambda, &lambda), x1), x2);
        let y3 = fr.subf(&fr.mulf(&lambda, &fr.subf(x1, &x3)), y1);
        (x3, y3)
    };

    // Assert addition outputs match
    assert_eq!(g3_runtime_normalized.0, g3_affine.0);
    assert_eq!(g3_runtime_normalized.1, g3_affine.1);

    // Test scalar_mul doubling
    let g2_scalar = scalar_mul(curve, fr, 2, &C::N::from_u64(2), &g);
    let g2_scalar_normalized = affine(fr, &g2_scalar);
    assert_eq!(g2_runtime_normalized.0, g2_scalar_normalized.0);
    assert_eq!(g2_runtime_normalized.1, g2_scalar_normalized.1);

    // Test scalar_mul tripling
    let g3_scalar = scalar_mul(curve, fr, 2, &C::N::from_u64(3), &g);
    let g3_scalar_normalized = affine(fr, &g3_scalar);
    assert_eq!(g3_runtime_normalized.0, g3_scalar_normalized.0);
    assert_eq!(g3_runtime_normalized.1, g3_scalar_normalized.1);
}

#[test]
fn test_ec_runtime_arithmetic_robust() {
    let fr = P256Field::new();
    let curve = Secp256r1::new(&fr);
    test_ec_runtime_arithmetic_robust_generic::<4, _, _>(&curve, &fr);
}

fn test_ec_circuit_evaluation_generic<
    const W: usize,
    F: CompileField + SupportsNatConversions<W>,
    C: Curve<W, F = F>,
>(
    curve: &C,
    f: &F,
) {
    let tracker = AssertionScope::new();
    type L<'a, F> = EvalLogic<'a, F>;
    let l = L::new(f, &tracker);
    let ec_circuit = EcCircuit::new(&l, curve);

    // Generator coordinates
    let g_2d = curve.g();
    let g_wire = (l.konst(&g_2d.0), l.konst(&g_2d.1));

    // Project generator to projective coordinates
    let g_proj_wire = ec_circuit.projective(&g_wire);

    // Double G in circuit
    let g2_proj_wire = ec_circuit.double(&g_proj_wire);

    // Verify coordinates of 2G via point_equality
    let g2_runtime = double(curve, f, &projective(curve, f, g_2d));
    let g2_runtime_normalized = affine(f, &g2_runtime);

    let zinv_val = f.invert(&g2_proj_wire.2.value);
    let zinv_wire = l.konst(&zinv_val);
    let g2_normalized_wire = (
        l.konst(&g2_runtime_normalized.0),
        l.konst(&g2_runtime_normalized.1),
    );

    let eq_assertion = ec_circuit.point_equality(&g2_proj_wire, &zinv_wire, &g2_normalized_wire);
    eq_assertion.unwrap();
}

#[test]
fn test_ec_circuit_evaluation() {
    let f = P256Field::new();
    let curve = Secp256r1::new(&f);
    test_ec_circuit_evaluation_generic::<4, _, _>(&curve, &f);
}

fn run_test_ec_runtime_arithmetic<
    const W: usize,
    FR: CompileField + SupportsNatConversions<W>,
    C: Curve<W, F = FR>,
>(
    curve: &C,
    fr: &FR,
) {
    // Get curve generator point
    let g_2d = curve.g();
    let g = projective(curve, fr, g_2d);

    // test normalization
    let g_norm = affine(fr, &g);
    assert_eq!(g_norm.0, g_2d.0);
    assert_eq!(g_norm.1, g_2d.1);

    // Compute doubling via runtime
    let g2 = double(curve, fr, &g);
    let g2_normalized = affine(fr, &g2);

    // Compute doubling via standard affine formulas
    let g2_affine = {
        let (x, y) = g_2d;
        let three = fr.addf(&fr.one(), &fr.addf(&fr.one(), &fr.one()));
        let two = fr.addf(&fr.one(), &fr.one());
        let x_sq = fr.mulf(x, x);
        let a_val = curve.a();
        let num = fr.addf(&fr.mulf(&three, &x_sq), a_val);
        let den = fr.mulf(&two, y);
        let lambda = fr.mulf(&num, &fr.invert(&den));
        let two_x = fr.mulf(&two, x);
        let x3 = fr.subf(&fr.mulf(&lambda, &lambda), &two_x);
        let y3 = fr.subf(&fr.mulf(&lambda, &fr.subf(x, &x3)), y);
        (x3, y3)
    };

    println!(
        "DEBUG: test_ec_runtime_arithmetic g2_normalized.0 = {:?}",
        fr.to_bytes(&g2_normalized.0)
    );
    println!(
        "DEBUG: test_ec_runtime_arithmetic g2_affine.0 = {:?}",
        fr.to_bytes(&g2_affine.0)
    );
    assert_eq!(g2_normalized.0, g2_affine.0);
    assert_eq!(g2_normalized.1, g2_affine.1);

    // Compute addition via runtime (G + 2G = 3G)
    let g3 = add(curve, fr, &g, &g2);
    let g3_normalized = affine(fr, &g3);

    // Compute addition via standard affine formulas
    let g3_affine = {
        let (x1, y1) = g_2d;
        let (x2, y2) = &g2_affine;
        let num = fr.subf(y2, y1);
        let den = fr.subf(x2, x1);
        let lambda = fr.mulf(&num, &fr.invert(&den));
        let x3 = fr.subf(&fr.subf(&fr.mulf(&lambda, &lambda), x1), x2);
        let y3 = fr.subf(&fr.mulf(&lambda, &fr.subf(x1, &x3)), y1);
        (x3, y3)
    };

    assert_eq!(g3_normalized.0, g3_affine.0);
    assert_eq!(g3_normalized.1, g3_affine.1);

    // Test scalar_mul doubling
    let g2_scalar = scalar_mul(curve, fr, 2, &C::N::from_u64(2), &g);
    let g2_scalar_normalized = affine(fr, &g2_scalar);
    assert_eq!(g2_normalized.0, g2_scalar_normalized.0);
    assert_eq!(g2_normalized.1, g2_scalar_normalized.1);

    // Test scalar_mul tripling
    let g3_scalar = scalar_mul(curve, fr, 2, &C::N::from_u64(3), &g);
    let g3_scalar_normalized = affine(fr, &g3_scalar);
    assert_eq!(g3_normalized.0, g3_scalar_normalized.0);
    assert_eq!(g3_normalized.1, g3_scalar_normalized.1);

    // Test scalar_mul by order yields zero point at infinity
    let inf = scalar_mul(curve, fr, 256, &curve.order(), &g);
    assert!(fr.is_zero(&inf.2));
}

#[test]
fn test_ec_runtime_arithmetic() {
    let fr = P256Field::new();
    let curve = Secp256r1::new(&fr);
    run_test_ec_runtime_arithmetic::<4, _, _>(&curve, &fr);
}

struct GenericWeierstrassCurve<F: AlgebraicField, N> {
    a: ElementOf<F>,
    b: ElementOf<F>,
    g: (ElementOf<F>, ElementOf<F>),
    order: N,
}

impl<const W: usize, F: AlgebraicField, N: Nat<W>> Curve<W> for GenericWeierstrassCurve<F, N> {
    type F = F;
    type N = N;

    fn order(&self) -> Self::N {
        self.order.clone()
    }

    fn a(&self) -> &ElementOf<Self::F> {
        &self.a
    }

    fn b(&self) -> &ElementOf<Self::F> {
        &self.b
    }

    fn g(&self) -> &(ElementOf<Self::F>, ElementOf<Self::F>) {
        &self.g
    }
}

fn assert_karatsuba_equals_bilinear_grid<const W: usize, F: CompileField, C: Curve<W, F = F>>(
    curve: &C,
    f: &F,
    grid: &[ElementOf<F>; 3],
) {
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(f, &tracker);
    let ec = EcCircuit::new(&l, curve);

    // Every coordinate of `add_karatsuba` and `add_bilinear` is a 6-variable polynomial in
    // `F[X1, Y1, Z1, X2, Y2, Z2]` of individual degree <= 2 in each variable. By multivariate
    // Lagrange interpolation uniqueness (Combinatorial Nullstellensatz), agreement on all
    // `3^6 = 729` points of `S^6` (`|S| = 3`) is a deductive proof of formal polynomial identity.
    assert!(grid[0] != grid[1] && grid[0] != grid[2] && grid[1] != grid[2]);

    let mut count = 0usize;
    for x1 in grid {
        for y1 in grid {
            for z1 in grid {
                for x2 in grid {
                    for y2 in grid {
                        for z2 in grid {
                            let p1 = (l.konst(x1), l.konst(y1), l.konst(z1));
                            let p2 = (l.konst(x2), l.konst(y2), l.konst(z2));
                            let orig = ec.add_karatsuba(&p1, &p2);
                            let bilin = ec.add_bilinear(&p1, &p2);
                            let dflt = ec.add(&p1, &p2);
                            let native = add(
                                curve,
                                f,
                                &(x1.clone(), y1.clone(), z1.clone()),
                                &(x2.clone(), y2.clone(), z2.clone()),
                            );
                            assert_eq!(orig.0.value, bilin.0.value, "X3 mismatch at grid #{count}");
                            assert_eq!(orig.1.value, bilin.1.value, "Y3 mismatch at grid #{count}");
                            assert_eq!(orig.2.value, bilin.2.value, "Z3 mismatch at grid #{count}");
                            assert_eq!(orig.0.value, dflt.0.value);
                            assert_eq!(orig.1.value, dflt.1.value);
                            assert_eq!(orig.2.value, dflt.2.value);
                            assert_eq!(orig.0.value, native.0);
                            assert_eq!(orig.1.value, native.1);
                            assert_eq!(orig.2.value, native.2);
                            count += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(count, 729);
}

#[test]
fn test_ec_add_formal_polynomial_identity_eval() {
    use crate::core::algebra::SupportsU64Conversions;

    let f = P256Field::new();
    let secp = Secp256r1::new(&f);

    let grid_small = [f.zero(), f.one(), f.u64_to_element(2)];
    assert_karatsuba_equals_bilinear_grid(&secp, &f, &grid_small);

    let grid_mixed = [f.zero(), f.mone(), secp.g().0.clone()];
    assert_karatsuba_equals_bilinear_grid(&secp, &f, &grid_mixed);

    // Also prove formal polynomial identity on a generic curve with `a != 0` and `a != -3`
    // (`a = 7, b = 11`), ensuring no `a`- or `3b`-weighted terms could vacuously cancel.
    let generic_curve = GenericWeierstrassCurve {
        a: f.u64_to_element(7),
        b: f.u64_to_element(11),
        g: secp.g().clone(),
        order: secp.order(),
    };
    assert_karatsuba_equals_bilinear_grid(&generic_curve, &f, &grid_small);
    assert_karatsuba_equals_bilinear_grid(&generic_curve, &f, &grid_mixed);
}

#[test]
fn test_ec_add_formal_polynomial_identity_compiled_v2() {
    use crate::core::algebra::SupportsU64Conversions;

    let fc = P256Field::new();
    let fr = crate::runtime::algebra::p256::P256Field::new();
    let generic_curve = GenericWeierstrassCurve {
        a: fc.u64_to_element(7),
        b: fc.u64_to_element(11),
        g: Secp256r1::new(&fc).g().clone(),
        order: Secp256r1::new(&fc).order(),
    };

    let generic_curve_r = GenericWeierstrassCurve {
        a: fr.u64_to_element(7),
        b: fr.u64_to_element(11),
        g: (
            fr.bytes_to_element(&fc.to_bytes(&generic_curve.g.0))
                .unwrap(),
            fr.bytes_to_element(&fc.to_bytes(&generic_curve.g.1))
                .unwrap(),
        ),
        order: generic_curve.order.clone(),
    };

    let (circuit, _stats, symbols) = compile(&fc, |iologic| {
        let ec = EcCircuit::new(&iologic, &generic_curve);
        let mut pos = K_FIRST_WIRE_POSITION;
        let p1 = (
            iologic.next(&mut pos),
            iologic.next(&mut pos),
            iologic.next(&mut pos),
        );
        let p2 = (
            iologic.next(&mut pos),
            iologic.next(&mut pos),
            iologic.next(&mut pos),
        );
        let expected_out = (
            iologic.next(&mut pos),
            iologic.next(&mut pos),
            iologic.next(&mut pos),
        );
        let orig = ec.add_karatsuba(&p1, &p2);
        let bilin = ec.add_bilinear(&p1, &p2);
        // Keep the independently computed native outputs as inputs so later
        // algebraic simplification cannot erase every equality and input.
        let assertions = iologic.assert_all(
            "ec_add_output",
            &[
                iologic.assert_eq("original_x3_eq", &orig.0, &expected_out.0),
                iologic.assert_eq("original_y3_eq", &orig.1, &expected_out.1),
                iologic.assert_eq("original_z3_eq", &orig.2, &expected_out.2),
                iologic.assert_eq("x3_eq", &bilin.0, &expected_out.0),
                iologic.assert_eq("y3_eq", &bilin.1, &expected_out.1),
                iologic.assert_eq("z3_eq", &bilin.2, &expected_out.2),
            ],
        );
        (assertions, 1, 0)
    });

    let grid_r = [fr.zero(), fr.mone(), fr.u64_to_element(5)];
    let mut count = 0usize;
    for x1 in &grid_r {
        for y1 in &grid_r {
            for z1 in &grid_r {
                for x2 in &grid_r {
                    for y2 in &grid_r {
                        for z2 in &grid_r {
                            let out =
                                add(&generic_curve_r, &fr, &(*x1, *y1, *z1), &(*x2, *y2, *z2));
                            let mut inputs = initial_inputs(&fr);
                            for coord in [x1, y1, z1, x2, y2, z2, &out.0, &out.1, &out.2] {
                                push_eltw(*coord, &mut inputs);
                            }
                            eval_circuit_fc(&fc, &fr, &circuit, &symbols, &inputs)
                                .unwrap()
                                .assert_all_passed();
                            count += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(count, 729);
}

#[test]
fn test_ec_add_special_and_boundary_points() {
    use crate::core::algebra::SupportsU64Conversions;

    let f = P256Field::new();
    let curve = Secp256r1::new(&f);
    let tracker = AssertionScope::new();
    let l = EvalLogic::new(&f, &tracker);
    let ec = EcCircuit::new(&l, &curve);

    let g = projective(&curve, &f, curve.g());
    let neg_g = (g.0.clone(), f.subf(&f.zero(), &g.1), g.2.clone());
    let inf = (f.zero(), f.one(), f.zero());
    let inf_scaled = (f.zero(), f.u64_to_element(19), f.zero());
    let two_g = double(&curve, &f, &g);
    let three_g = add(&curve, &f, &g, &two_g);
    let twist_pt = (f.u64_to_element(2), f.u64_to_element(3), f.one());

    let two64 = f.mulf(&f.u64_to_element(1u64 << 32), &f.u64_to_element(1u64 << 32));
    let two128 = f.mulf(&two64, &two64);
    let two192 = f.mulf(&two128, &two64);
    let limb_pt_1 = (f.subf(&two64, &f.one()), two128.clone(), f.mone());
    let limb_pt_2 = (
        f.addf(&two192, &f.one()),
        f.u64_to_element(u64::MAX),
        two64.clone(),
    );

    let scale = |pt: &(
        ElementOf<P256Field>,
        ElementOf<P256Field>,
        ElementOf<P256Field>,
    ),
                 lam: &ElementOf<P256Field>| {
        (f.mulf(&pt.0, lam), f.mulf(&pt.1, lam), f.mulf(&pt.2, lam))
    };

    let lam1 = f.u64_to_element(0xdead_beef_cafe_babe);
    let lam2 = f.subf(&two128, &f.u64_to_element(17));
    let g_scaled = scale(&g, &lam1);
    let two_g_scaled = scale(&two_g, &lam2);

    let points = [
        inf.clone(),
        inf_scaled,
        g.clone(),
        neg_g.clone(),
        two_g.clone(),
        three_g,
        g_scaled.clone(),
        two_g_scaled.clone(),
        twist_pt,
        limb_pt_1,
        limb_pt_2,
    ];

    let to_wires = |pt: &(
        ElementOf<P256Field>,
        ElementOf<P256Field>,
        ElementOf<P256Field>,
    )| (l.konst(&pt.0), l.konst(&pt.1), l.konst(&pt.2));

    for p1 in &points {
        for p2 in &points {
            let w1 = to_wires(p1);
            let w2 = to_wires(p2);
            let orig = ec.add_karatsuba(&w1, &w2);
            let bilin = ec.add_bilinear(&w1, &w2);
            assert_eq!(orig.0.value, bilin.0.value);
            assert_eq!(orig.1.value, bilin.1.value);
            assert_eq!(orig.2.value, bilin.2.value);
        }
    }

    // Group-law checks on complete addition:
    // 1. P + (-P) = O = (0, Y3 != 0, 0)
    let sum_inv = ec.add_bilinear(&to_wires(&g), &to_wires(&neg_g));
    assert!(f.is_zero(&sum_inv.0.value));
    assert!(!f.is_zero(&sum_inv.1.value));
    assert!(f.is_zero(&sum_inv.2.value));

    // 2. P + P agrees with `double(P)` in affine coordinates
    let sum_same = ec.add_bilinear(&to_wires(&g), &to_wires(&g));
    let sum_same_aff = affine(
        &f,
        &(
            sum_same.0.value.clone(),
            sum_same.1.value.clone(),
            sum_same.2.value.clone(),
        ),
    );
    let dbl_aff = affine(&f, &two_g);
    assert_eq!(sum_same_aff, dbl_aff);

    // 3. Homogeneous degree-2 scaling in each point: add(lam1 * P1, lam2 * P2) == (lam1^2 * lam2^2)
    //    * add(P1, P2)
    let unscaled = ec.add_bilinear(&to_wires(&g), &to_wires(&two_g));
    let scaled = ec.add_bilinear(&to_wires(&g_scaled), &to_wires(&two_g_scaled));
    let factor = f.mulf(&f.mulf(&lam1, &lam1), &f.mulf(&lam2, &lam2));
    assert_eq!(scaled.0.value, f.mulf(&factor, &unscaled.0.value));
    assert_eq!(scaled.1.value, f.mulf(&factor, &unscaled.1.value));
    assert_eq!(scaled.2.value, f.mulf(&factor, &unscaled.2.value));
}
