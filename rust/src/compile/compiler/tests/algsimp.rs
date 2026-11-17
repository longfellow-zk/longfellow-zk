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

use crate::{
    compile::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, CompileField},
        compiler::{
            algsimp::AlgebraicRewriter,
            arena::CompilerArena,
            cse::Cse,
            ir::{Expr, RewriteT},
        },
    },
    core::algebra::{AlgebraicField, Nat, SupportsNatConversions, SupportsU64Conversions},
};

fn run_test<
    const W: usize,
    F: CompileField + SupportsNatConversions<W> + SupportsU64Conversions,
>(
    f: &F,
) {
    let arena = CompilerArena::new();
    let cse = Cse::new(&arena);
    let algebraic = AlgebraicRewriter::new(f, cse);

    // Constant folding
    let c1 = algebraic.constant(&f.u64_to_element(10));
    let c2 = algebraic.constant(&f.u64_to_element(20));
    let sum_nodes = algebraic.sum(&[c1, c2], false);

    match &sum_nodes.v {
        Expr::Constant(val) => {
            assert_eq!(f.to_nat(val), F::N::from_u64(30));
        }
        _ => panic!("Expected Constant(30), got {sum_nodes:?}"),
    }
}

#[test]
fn test_rewrite_algebraic_simplification() {
    let f = P256Field::new();
    run_test::<4, P256Field>(&f);
}

#[test]
fn test_algsimp_prime_cancel() {
    let f = P256Field::new();
    let arena = CompilerArena::new();
    let cse = Cse::new(&arena);
    let algebraic = AlgebraicRewriter::new(&f, cse);

    let x = algebraic.input(1);
    let neg_x = algebraic.linear(&f.mone(), &x);
    let sum = algebraic.sum(&[x, neg_x], false);

    match &sum.v {
        Expr::Constant(val) => {
            assert!(f.is_zero(val));
        }
        _ => panic!("Expected Constant(0), got {sum:?}"),
    }
}

#[test]
fn test_algsimp_binary_x_plus_x() {
    let f = Gf2_128Field::new();
    let arena = CompilerArena::new();
    let cse = Cse::new(&arena);
    let algebraic = AlgebraicRewriter::new(&f, cse);

    let x = algebraic.input(1);
    let sum = algebraic.sum(&[x, x], false);

    match &sum.v {
        Expr::Constant(val) => {
            assert!(f.is_zero(val));
        }
        _ => panic!("Expected Constant(0), got {sum:?}"),
    }
}

#[test]
fn binary_precious_sum_cancels_its_flattened_alias() {
    let f = Gf2_128Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::new(&f, Cse::new(&arena));
    let x = algebraic.input(1);
    let y = algebraic.input(2);
    let z = algebraic.input(3);
    let precious = algebraic.sum(&[x, y], true);
    let ordinary = algebraic.sum(&[x, y, z], false);

    // The containing ordinary sum has flattened x+y already, so there is no
    // direct ordinary alias for the old precious/ordinary-pair rule to detect.
    // Leaving precious(x+y)+x+y here made the copy pass reconstruct the same
    // wire twice, triggering the scheduler's duplicate-term invariant.
    let cancelled = algebraic.sum(&[precious, ordinary], false);
    assert_eq!(cancelled, z);

    // Partial overlap must retain the shared sum instead of flattening it.
    let partial = algebraic.sum(&[precious, x, z], false);
    let Expr::Sum(terms, _) = partial.v else {
        panic!("expected the partially overlapping sum to retain sharing");
    };
    assert!(terms.contains(&precious));
}

#[test]
fn prime_precious_sum_coalesces_its_flattened_alias() {
    let f = P256Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::new(&f, Cse::new(&arena));
    let x = algebraic.input(1);
    let y = algebraic.input(2);
    let z = algebraic.input(3);
    let precious = algebraic.sum(&[x, y], true);
    let ordinary = algebraic.sum(&[x, y, z], false);
    let actual = algebraic.sum(&[precious, ordinary], false);
    let two = f.u64_to_element(2);
    let expected = algebraic.sum(
        &[algebraic.linear(&two, &x), algebraic.linear(&two, &y), z],
        false,
    );
    assert_eq!(actual, expected);
}

#[test]
fn bilinear_2x2_expands_when_enabled() {
    let f = Gf2_128Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::with_bilinear_expansion(&f, Cse::new(&arena), true);
    let a = algebraic.input(1);
    let b = algebraic.input(2);
    let c = algebraic.input(3);
    let d = algebraic.input(4);

    let ab = algebraic.sum(&[a, b], false);
    let cd = algebraic.sum(&[c, d], false);
    let prod = algebraic.quadratic(&f.one(), &ab, &cd);

    let expected = algebraic.sum(
        &[
            algebraic.quadratic(&f.one(), &a, &c),
            algebraic.quadratic(&f.one(), &a, &d),
            algebraic.quadratic(&f.one(), &b, &c),
            algebraic.quadratic(&f.one(), &b, &d),
        ],
        false,
    );
    assert_eq!(prod, expected);

    // Low-degree constant summands `(a + 1) * (b + 1)` also fold cleanly to `a*b + a + b + 1`.
    let one = algebraic.one();
    let a1 = algebraic.sum(&[a, one], false);
    let b1 = algebraic.sum(&[b, one], false);
    let prod_const = algebraic.quadratic(&f.one(), &a1, &b1);
    let expected_const = algebraic.sum(&[algebraic.quadratic(&f.one(), &a, &b), a, b, one], false);
    assert_eq!(prod_const, expected_const);
}

#[test]
fn bilinear_2x2_not_expanded_when_disabled() {
    let f = Gf2_128Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::new(&f, Cse::new(&arena));
    let a = algebraic.input(1);
    let b = algebraic.input(2);
    let c = algebraic.input(3);
    let d = algebraic.input(4);

    let ab = algebraic.sum(&[a, b], false);
    let cd = algebraic.sum(&[c, d], false);
    let prod = algebraic.quadratic(&f.one(), &ab, &cd);

    assert!(
        matches!(&prod.v, Expr::Quadratic(_, x, y) if (*x == ab && *y == cd) || (*x == cd && *y == ab)),
        "expected unexpanded Quadratic over (a+b) and (c+d), got {prod:?}"
    );
}

#[test]
fn bilinear_not_expanded_when_len_exceeds_two() {
    let f = P256Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::with_bilinear_expansion(&f, Cse::new(&arena), true);
    let a = algebraic.input(1);
    let b = algebraic.input(2);
    let c = algebraic.input(3);
    let d = algebraic.input(4);
    let e = algebraic.input(5);

    let abc = algebraic.sum(&[a, b, c], false);
    let de = algebraic.sum(&[d, e], false);

    let lhs_3x2 = algebraic.quadratic(&f.one(), &abc, &de);
    assert!(
        matches!(&lhs_3x2.v, Expr::Quadratic(_, x, y) if (*x == abc && *y == de) || (*x == de && *y == abc)),
        "expected 3x2 product to stay unexpanded, got {lhs_3x2:?}"
    );

    let rhs_2x3 = algebraic.quadratic(&f.one(), &de, &abc);
    assert!(
        matches!(&rhs_2x3.v, Expr::Quadratic(_, x, y) if (*x == abc && *y == de) || (*x == de && *y == abc)),
        "expected 2x3 product to stay unexpanded, got {rhs_2x3:?}"
    );
}

#[test]
fn bilinear_not_expanded_when_precious() {
    let f = P256Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::with_bilinear_expansion(&f, Cse::new(&arena), true);
    let a = algebraic.input(1);
    let b = algebraic.input(2);
    let c = algebraic.input(3);
    let d = algebraic.input(4);

    let precious_ab = algebraic.sum(&[a, b], true);
    let cd = algebraic.sum(&[c, d], false);

    let lhs_precious = algebraic.quadratic(&f.one(), &precious_ab, &cd);
    assert!(
        matches!(&lhs_precious.v, Expr::Quadratic(_, x, y) if (*x == precious_ab && *y == cd) || (*x == cd && *y == precious_ab)),
        "expected precious*ordinary product to stay unexpanded, got {lhs_precious:?}"
    );

    let rhs_precious = algebraic.quadratic(&f.one(), &cd, &precious_ab);
    assert!(
        matches!(&rhs_precious.v, Expr::Quadratic(_, x, y) if (*x == precious_ab && *y == cd) || (*x == cd && *y == precious_ab)),
        "expected ordinary*precious product to stay unexpanded, got {rhs_precious:?}"
    );
}

#[test]
fn bilinear_not_expanded_when_summand_not_low_degree() {
    let f = P256Field::new();
    let arena = CompilerArena::new();
    let algebraic = AlgebraicRewriter::with_bilinear_expansion(&f, Cse::new(&arena), true);
    let a = algebraic.input(1);
    let b = algebraic.input(2);
    let c = algebraic.input(3);
    let d = algebraic.input(4);
    let e = algebraic.input(5);

    let ab_prod = algebraic.quadratic(&f.one(), &a, &b);
    let high_deg_sum = algebraic.sum(&[ab_prod, c], false);
    let de = algebraic.sum(&[d, e], false);

    let lhs_high = algebraic.quadratic(&f.one(), &high_deg_sum, &de);
    assert!(
        matches!(&lhs_high.v, Expr::Quadratic(_, x, y) if (*x == high_deg_sum && *y == de) || (*x == de && *y == high_deg_sum)),
        "expected product with quadratic summand on LHS to stay unexpanded, got {lhs_high:?}"
    );

    let rhs_high = algebraic.quadratic(&f.one(), &de, &high_deg_sum);
    assert!(
        matches!(&rhs_high.v, Expr::Quadratic(_, x, y) if (*x == high_deg_sum && *y == de) || (*x == de && *y == high_deg_sum)),
        "expected product with quadratic summand on RHS to stay unexpanded, got {rhs_high:?}"
    );

    let precious_ab = algebraic.sum(&[a, b], true);
    let nested_precious_sum = algebraic.sum(&[precious_ab, c], false);
    let nested_prod = algebraic.quadratic(&f.one(), &nested_precious_sum, &de);
    assert!(
        matches!(&nested_prod.v, Expr::Quadratic(_, x, y) if (*x == nested_precious_sum && *y == de) || (*x == de && *y == nested_precious_sum)),
        "expected product with precious summand to stay unexpanded, got {nested_prod:?}"
    );
}
