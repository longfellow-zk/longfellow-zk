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

//! Shared arithmetic and canonical encoding of `F_q[x] / (x^6 - 7)`.

use super::fp24::{add_base, invert_base, mul_base, sub_base};
pub use super::fp24::{BASE_SERIALIZED_SIZE, Q};

pub const BETA: u32 = 7;
pub const EXTENSION_DEGREE: usize = 6;
pub const SERIALIZED_SIZE: usize = BASE_SERIALIZED_SIZE * EXTENSION_DEGREE;

pub(crate) fn add_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    for i in 0..EXTENSION_DEGREE {
        a[i] = add_base(a[i], b[i]);
    }
}

pub(crate) fn sub_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    for i in 0..EXTENSION_DEGREE {
        a[i] = sub_base(a[i], b[i]);
    }
}

#[inline]
pub(crate) fn product_unreduced(
    a: &[u32; EXTENSION_DEGREE],
    b: &[u32; EXTENSION_DEGREE],
) -> [u64; 2 * EXTENSION_DEGREE - 1] {
    let mut product = [0u64; 2 * EXTENSION_DEGREE - 1];
    for i in 0..EXTENSION_DEGREE {
        for j in 0..EXTENSION_DEGREE {
            product[i + j] += u64::from(a[i]) * u64::from(b[j]);
        }
    }
    product
}

pub(crate) fn mul_extension(a: &mut [u32; EXTENSION_DEGREE], b: &[u32; EXTENSION_DEGREE]) {
    let mut product = product_unreduced(a, b);
    for i in 0..(EXTENSION_DEGREE - 1) {
        product[i] += product[i + EXTENSION_DEGREE] * u64::from(BETA);
    }
    for i in 0..EXTENSION_DEGREE {
        a[i] = (product[i] % u64::from(Q)) as u32;
    }
}

pub(crate) fn invert_extension(a: &[u32; EXTENSION_DEGREE]) -> [u32; EXTENSION_DEGREE] {
    assert!(
        a.iter().any(|&coefficient| coefficient != 0),
        "cannot invert zero"
    );

    if a[1..].iter().all(|&coefficient| coefficient == 0) {
        let mut result = [0; EXTENSION_DEGREE];
        result[0] = invert_base(a[0]);
        return result;
    }

    // Multiplication by `a` is a beta-circulant matrix. Solve a*x = 1 over F_q.
    let mut matrix = [[0u32; EXTENSION_DEGREE]; EXTENSION_DEGREE];
    for row in 0..EXTENSION_DEGREE {
        for column in 0..EXTENSION_DEGREE {
            matrix[row][column] = if row >= column {
                a[row - column]
            } else {
                mul_base(a[row + EXTENSION_DEGREE - column], BETA)
            };
        }
    }
    let mut result = [0u32; EXTENSION_DEGREE];
    result[0] = 1;

    for column in 0..EXTENSION_DEGREE {
        let pivot = (column..EXTENSION_DEGREE)
            .find(|&row| matrix[row][column] != 0)
            .expect("extension polynomial must define a field");
        if pivot != column {
            matrix.swap(column, pivot);
            result.swap(column, pivot);
        }

        let scale = invert_base(matrix[column][column]);
        for entry in &mut matrix[column][column..] {
            *entry = mul_base(*entry, scale);
        }
        result[column] = mul_base(result[column], scale);

        let pivot_row = matrix[column];
        let pivot_result = result[column];
        for row in 0..EXTENSION_DEGREE {
            if row == column {
                continue;
            }
            let factor = matrix[row][column];
            for (j, entry) in matrix[row].iter_mut().enumerate().skip(column) {
                *entry = sub_base(*entry, mul_base(factor, pivot_row[j]));
            }
            result[row] = sub_base(result[row], mul_base(factor, pivot_result));
        }
    }
    result
}

pub(crate) fn serialize(coefficients: &[u32; EXTENSION_DEGREE], dst: &mut [u8]) {
    assert_eq!(dst.len(), SERIALIZED_SIZE);
    for (coefficient, bytes) in coefficients
        .iter()
        .zip(dst.as_chunks_mut::<BASE_SERIALIZED_SIZE>().0.iter_mut())
    {
        bytes.copy_from_slice(&coefficient.to_le_bytes()[..BASE_SERIALIZED_SIZE]);
    }
}

pub(crate) fn deserialize(bytes: &[u8]) -> Result<[u32; EXTENSION_DEGREE], String> {
    if bytes.len() != SERIALIZED_SIZE {
        return Err(format!(
            "invalid Fp24 sextic extension element size: {}",
            bytes.len()
        ));
    }
    let mut coefficients = [0u32; EXTENSION_DEGREE];
    for (coefficient, chunk) in coefficients
        .iter_mut()
        .zip(bytes.as_chunks::<BASE_SERIALIZED_SIZE>().0.iter())
    {
        *coefficient = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], 0]);
        if *coefficient >= Q {
            return Err("non-canonical Fp24 sextic extension coefficient".to_owned());
        }
    }
    Ok(coefficients)
}
