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

use super::{
    constants::K,
    shape::{Derived, Given},
};

#[inline]
fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

#[inline]
fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

#[inline]
fn sigma0_upper(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

#[inline]
fn sigma1_upper(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

#[inline]
fn sigma0_lower(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

#[inline]
fn sigma1_lower(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

#[must_use]
pub fn derived(given: &Given<u32>) -> Derived<u32> {
    let mut w = [0u32; 64];
    w[..16].copy_from_slice(&given.input_block);
    for i in 16..64 {
        let s0 = sigma0_lower(w[i - 15]);
        let s1 = sigma1_lower(w[i - 2]);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }

    let mut a = given.h0[0];
    let mut b = given.h0[1];
    let mut c = given.h0[2];
    let mut d = given.h0[3];
    let mut e = given.h0[4];
    let mut f = given.h0[5];
    let mut g = given.h0[6];
    let mut h = given.h0[7];

    let mut oute = [0u32; 64];
    let mut outa = [0u32; 64];

    for i in 0..64 {
        let s1 = sigma1_upper(e);
        let ch_val = ch(e, f, g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(ch_val)
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let s0 = sigma0_upper(a);
        let maj_val = maj(a, b, c);
        let temp2 = s0.wrapping_add(maj_val);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);

        oute[i] = e;
        outa[i] = a;
    }

    let h1 = [
        given.h0[0].wrapping_add(a),
        given.h0[1].wrapping_add(b),
        given.h0[2].wrapping_add(c),
        given.h0[3].wrapping_add(d),
        given.h0[4].wrapping_add(e),
        given.h0[5].wrapping_add(f),
        given.h0[6].wrapping_add(g),
        given.h0[7].wrapping_add(h),
    ];

    let mut outw = [0u32; 48];
    outw.copy_from_slice(&w[16..64]);

    Derived {
        outw,
        oute,
        outa,
        h1,
    }
}

cfg_testonly! {
    impl Derived<u32> {
        pub fn push_derived<FR: crate::runtime::algebra::RuntimeField>(
            &self,
            fr: &FR,
            mut push: impl FnMut(FR::E),
        ) {
            let mut dest = Vec::with_capacity(168 * 32);
            self.for_each(|&val| {
                crate::circuits::bitvec::push_bitvec_u64(fr, u64::from(val), 32, &mut dest);
            });
            for e in dest {
                push(e);
            }
        }
    }
}
