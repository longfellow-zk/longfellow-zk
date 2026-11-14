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

//! Arithmetic modulo the prime `q = 8_380_417`.
//! Shared by the compiler and runtime sextic fields.

pub const Q: u32 = 8_380_417;
pub const BASE_SERIALIZED_SIZE: usize = 3;

#[inline]
pub(crate) fn add_base(a: u32, b: u32) -> u32 {
    let sum = a + b;
    if sum >= Q {
        sum - Q
    } else {
        sum
    }
}

#[inline]
pub(crate) fn sub_base(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        a + Q - b
    }
}

#[inline]
pub(crate) fn mul_base(a: u32, b: u32) -> u32 {
    (u64::from(a) * u64::from(b) % u64::from(Q)) as u32
}

pub(crate) fn invert_base(value: u32) -> u32 {
    assert_ne!(value, 0, "cannot invert zero");
    // Binary extended GCD is materially faster here than exponentiation by
    // q-2. Keep the coefficients reduced in F_q, matching Fp24 in C++.
    let mut a = value;
    let mut b = Q;
    let mut u = 1;
    let mut v = 0;
    while a != 0 {
        if a & 1 == 0 {
            a >>= 1;
            u = half_base(u);
        } else {
            if a < b {
                std::mem::swap(&mut a, &mut b);
                std::mem::swap(&mut u, &mut v);
            }
            a = (a - b) >> 1;
            u = half_base(sub_base(u, v));
        }
    }
    v
}

#[inline]
fn half_base(a: u32) -> u32 {
    if a & 1 == 0 {
        a >> 1
    } else {
        (a >> 1) + Q.div_ceil(2)
    }
}
