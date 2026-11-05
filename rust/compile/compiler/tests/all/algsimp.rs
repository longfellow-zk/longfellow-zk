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
        algebra::{
            field::{CompileField, SupportsNatConversions, SupportsU64Conversions},
            gf2_128::Gf2_128Field,
            p256::P256Field,
            AlgebraicField,
        },
        compiler::{
            algsimp::AlgebraicRewriter,
            arena::CompilerArena,
            cse::Cse,
            ir::{Expr, RewriteT},
        },
    },
    core::algebra::Nat,
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
