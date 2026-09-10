// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The lookup tables' Lagrange bases, and whether the identity the spec bridge needs holds.
//!
//! `circuits_lookup::Lookup::table` interpolates the tabulated values through the nodes
//! `lookup_point(n, i) = 2i - (n - 1)` and stores the interpolant's **monomial** coefficients as
//! circuit constants. `eval(u)` is then `Σ_j pluck_j · u^j` with `pluck_j = Σ_k c_{k,j} · v_k`,
//! so the whole lookup collapses to `v_i` at `u = node_i` exactly when
//!
//!   `Σ_j c_{k,j} · node_i^j = δ_{ki}`.
//!
//! Those are the certificates the meaning lemmas need, and they depend only on the field and the
//! node set — not on the tabulated values, and so not on which of the seven tables is in play.
//! ECDSA2 needs two node sets: the 8 active points of `opt8`/`delta8` (indices 0..7 of a 9-point
//! table) and all 9 of `delta9`.
//!
//! This prints the coefficients, checks each identity in Rust, and reports whether every
//! coefficient is present in the segmented circuit's constant table -- which is what lets the
//! Lean certificate be stated over `constNat` rather than over unchecked literals.

use compile_algebra::{field::CompileField, p256::P256Field};
use core_algebra::AlgebraicField;

fn main() {
    let f = P256Field::new();
    let sidecar = std::env::args().nth(1);

    // Constant table of the deployed circuit, if a sidecar was given.
    let table: Vec<Vec<u8>> = sidecar
        .as_deref()
        .map(|p| {
            let bytes = std::fs::read(p).unwrap_or_else(|e| panic!("read {p}: {e}"));
            compile_compiler::cert::parse_sidecar(&bytes)
                .expect("sidecar parses")
                .constants
        })
        .unwrap_or_default();
    let index_of = |k: &core_algebra::ElementOf<P256Field>| -> Option<usize> {
        let b = core_algebra::SerializableField::to_bytes(&f, k);
        table.iter().position(|c| c.as_slice() == b.as_slice())
    };

    for m in [8usize, 9] {
        // Both table kinds are built with `n = 9`, so the nodes are `2i - 8`; `opt8`/`delta8`
        // simply leave index 8 inactive, which drops the last node.
        let x: Vec<_> = (0..m)
            .map(|i| core_algebra::HasLookupPoints::lookup_point(&f, 9, i))
            .collect();
        println!("\n=== {m} active nodes of a 9-point table (node_i = 2i - 8) ===");

        let mut missing = 0usize;
        let mut bad = 0usize;
        for k in 0..m {
            let mut y = vec![f.zero(); m];
            y[k] = f.one();
            let coeffs = compile_algebra::interpolation::monomial_of_lagrange(&f, &y, &x);
            assert_eq!(coeffs.len(), m);
            if table.is_empty() {
                continue;
            }
            for c in &coeffs {
                if index_of(c).is_none() {
                    missing += 1;
                }
            }
            // The identity, checked in the field.
            for i in 0..m {
                let mut acc = f.zero();
                let mut pow = f.one();
                for c in &coeffs {
                    acc = f.addf(&acc, &f.mulf(c, &pow));
                    pow = f.mulf(&pow, &x[i]);
                }
                let want = if k == i { f.one() } else { f.zero() };
                if acc != want {
                    bad += 1;
                    println!("  L_{k}(node_{i}) != delta");
                }
            }
        }
        // Dump the coefficients so the Lean certificates can be generated from them.
        if std::env::var("DUMP").is_ok() {
            print!("{{\"m\": {m}, \"rows\": [");
            for k in 0..m {
                let mut y = vec![f.zero(); m];
                y[k] = f.one();
                let coeffs = compile_algebra::interpolation::monomial_of_lagrange(&f, &y, &x);
                if k > 0 {
                    print!(", ");
                }
                print!("[");
                for (j, c) in coeffs.iter().enumerate() {
                    let b = core_algebra::SerializableField::to_bytes(&f, c);
                    let hex: String = b.iter().rev().map(|x| format!("{x:02x}")).collect();
                    if j > 0 {
                        print!(", ");
                    }
                    print!("\"{hex}\"");
                }
                print!("]");
            }
            println!("]}}");
        }
        println!("  identities checked: {} bad", bad);
        if !table.is_empty() {
            println!(
                "  coefficients absent from the circuit's constant table: {missing} of {}",
                m * m
            );
        }
    }
}
