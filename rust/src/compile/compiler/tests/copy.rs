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
        algebra::{p256::P256Field, CompileField},
        compiler::{
            arena::CompilerArena,
            cse::Cse,
            ir::{Expr, RewriteT},
            v1::copy::CopyRewriter as V1CopyRewriter,
            v2::copy::CopyRewriter as V2CopyRewriter,
        },
    },
    core::algebra::{Nat, SupportsNatConversions, SupportsU64Conversions},
};

fn run_v1_test<
    const W: usize,
    F: CompileField + SupportsNatConversions<W> + SupportsU64Conversions,
>(
    f: &F,
) {
    let arena = CompilerArena::new();
    let cse = Cse::new(&arena);

    let copy_rewriter = V1CopyRewriter::new(f, cse);

    // v1 folds constants to Quadratic(k, One, One).
    let c1 = copy_rewriter.constant(&f.u64_to_element(10));
    match &c1.v {
        Expr::Quadratic(val, x, y) => {
            assert_eq!(f.to_nat(val), F::N::from_u64(10));
            assert!(matches!(x.v, Expr::One));
            assert!(matches!(y.v, Expr::One));
        }
        _ => panic!("Expected Quadratic(10, One, One), got {c1:?}"),
    }
}

fn run_v2_test<
    const W: usize,
    F: CompileField + SupportsNatConversions<W> + SupportsU64Conversions,
>(
    f: &F,
) {
    let arena = CompilerArena::new();
    let cse = Cse::new(&arena);

    let copy_rewriter = V2CopyRewriter::new(f, cse);

    // v2 keeps constants native (no One node) and aligns depths via Linear(1, x).
    let c1 = copy_rewriter.constant(&f.u64_to_element(10));
    match &c1.v {
        Expr::Constant(val) => assert_eq!(f.to_nat(val), F::N::from_u64(10)),
        _ => panic!("Expected Constant(10), got {c1:?}"),
    }

    let x1 = copy_rewriter.input(1);
    let x2 = copy_rewriter.input(2);
    let x3 = copy_rewriter.input(3);
    let p23 = copy_rewriter.quadratic(&f.u64_to_element(1), &x2, &x3);
    let p123 = copy_rewriter.quadratic(&f.u64_to_element(1), &x1, &p23);
    match &p123.v {
        Expr::Quadratic(_, left, right) => {
            assert_eq!(left.depth, 1);
            assert_eq!(right.depth, 1);
            let copied = if matches!(left.v, Expr::Linear(..)) {
                left
            } else {
                right
            };
            match &copied.v {
                Expr::Linear(k, inner) => {
                    assert_eq!(*k, &f.one());
                    assert_eq!(*inner, x1);
                }
                _ => panic!("Expected Linear(1, x1) copy wire, got {copied:?}"),
            }
        }
        _ => panic!("Expected Quadratic, got {p123:?}"),
    }
}

#[test]
fn test_rewrite_copy() {
    let f = P256Field::new();
    run_v1_test::<4, P256Field>(&f);
    run_v2_test::<4, P256Field>(&f);
}
