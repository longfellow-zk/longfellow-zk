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

// ARMv7 NEON intrinsics are unstable in Rust. Inline assembly keeps this
// backend usable on stable. The arm-neon Cargo feature selects it at build
// time; the build must also enable -C target-feature=+neon. No runtime dispatch.
// Without that feature (or with force-generic-arch), ARM uses scalar code.
use core::arch::asm;

// Register audit (qN aliases d(2N), d(2N+1)):
//   q0: product/result; q1-q3: multiplication/reduction scratch;
//   q4-q5: low/high Karatsuba products; d16-d21: operands/shuffle scratch;
//   q11-q12: inputs, preserved by products_in_registers!;
//   q6-q7 and q13-q15: untouched.
// Every written D register is an output/clobber below. In particular d8-d11
// are callee-saved, so LLVM must preserve them at function boundaries.
// Memory kernels use byte loads/stores with no extra alignment assertion,
// declare memory effects, and use early inout operands for writeback pointers.
// The arithmetic has fixed instruction counts and no secret-indexed memory.
// Enable NEON through the compiler flags, not a local .fpu directive: inline
// assembly must leave the surrounding assembler state unchanged.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[repr(transparent)]
pub struct Gf2_128(pub u128);

// Karatsuba coefficients: t0 + X^64 * (t1 ^ t0 ^ t2) + X^128 * t2.
// Reduction accepts arbitrary coefficients, including bit 127 of each.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Gf2_128Accum(pub [Gf2_128; 3]);

impl Gf2_128 {
    #[inline(always)]
    pub const fn from_u128(v: u128) -> Self {
        Self(v)
    }

    #[inline(always)]
    pub const fn to_u128(&self) -> u128 {
        self.0
    }

    #[inline(always)]
    pub fn xor_in_place(&mut self, other: &Self) {
        self.0 ^= other.0;
    }

    #[inline(always)]
    pub fn xor(&self, other: &Self) -> Self {
        Self(self.0 ^ other.0)
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

// 64-bit carry-less multiplication: d16 * d17 -> q0. q3 must be zero;
// d0-d5 and d18-d21 are scratch. The diagonal byte-product algorithm
// matches lib/gf2k/sysdep.h. Each 64-bit product uses 15 VMULL.P8s.
macro_rules! pmul64_in_registers {
    () => {
        concat!(
            "vext.8 d18, d16, d6, #1\n",
            "vext.8 d19, d17, d6, #1\n",
            "vmull.p8 q0, d16, d17\n",
            "vmull.p8 q1, d18, d17\n",
            "vmull.p8 q2, d16, d19\n",
            "veor q1, q1, q2\n",
            "vext.8 d20, d6, d16, #7\n",
            "vext.8 d21, d6, d17, #7\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q0, q0, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q0, q0, q2\n",
            "vext.8 d18, d18, d6, #1\n",
            "vext.8 d19, d19, d6, #1\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q1, q1, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q1, q1, q2\n",
            "vext.8 d20, d6, d20, #7\n",
            "vext.8 d21, d6, d21, #7\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q0, q0, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q0, q0, q2\n",
            "vext.8 d18, d18, d6, #1\n",
            "vext.8 d19, d19, d6, #1\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q1, q1, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q1, q1, q2\n",
            "vext.8 d20, d6, d20, #7\n",
            "vext.8 d21, d6, d21, #7\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q0, q0, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q0, q0, q2\n",
            "vext.8 d18, d18, d6, #1\n",
            "vext.8 d19, d19, d6, #1\n",
            "vmull.p8 q2, d20, d19\n",
            "veor q1, q1, q2\n",
            "vmull.p8 q2, d18, d21\n",
            "veor q1, q1, q2\n",
            "vext.8 q2, q3, q1, #15\n",
            "veor q0, q0, q2\n",
        )
    };
}

// Reduce q0 + X^64 * q1; return q0 and clobber q2, q3, and d16.
macro_rules! reduce_in_registers {
    () => {
        concat!(
            "veor q2, q2, q2\n",
            "vext.8 q3, q2, q1, #8\n",
            "veor q0, q0, q3\n",
            "vmov.i8 d16, #0x87\n",
            "vmull.p8 q3, d3, d16\n",
            "vuzp.8 q3, q2\n",
            "vext.8 q2, q2, q2, #15\n",
            "veor q0, q0, q3\n",
            "veor q0, q0, q2\n",
        )
    };
}

// Karatsuba products for q11 * q12: low -> q4, high -> q5, and the
// product of XORed halves -> q0. Inputs q11/q12 survive; d0-d11 and
// d16-d21 are scratch. Keeping all three products live avoids stack spills.
macro_rules! products_in_registers {
    () => {
        concat!(
            "veor q3, q3, q3\n",
            "vmov d16, d22\n",
            "vmov d17, d24\n",
            pmul64_in_registers!(),
            "vmov q4, q0\n",
            "vmov d16, d23\n",
            "vmov d17, d25\n",
            pmul64_in_registers!(),
            "vmov q5, q0\n",
            "veor d16, d22, d23\n",
            "veor d17, d24, d25\n",
            pmul64_in_registers!(),
        )
    };
}

// Combine the Karatsuba products and reduce twice, returning q0.
macro_rules! finish_in_registers {
    () => {
        concat!(
            "veor q0, q0, q4\n",
            "veor q0, q0, q5\n",
            "vmov q1, q5\n",
            reduce_in_registers!(),
            "vmov q1, q0\n",
            "vmov q0, q4\n",
            reduce_in_registers!(),
        )
    };
}

// SAFETY: the CPU must support NEON. All three Karatsuba products and both
// reductions stay in registers. Integer operands in D registers avoid
// memory clobbers, letting LLVM reuse surrounding loads and XORs. The
// arm-neon build feature makes NEON a requirement for the whole binary.
#[inline(always)]
pub fn gf2_128_mul(x: Gf2_128, y: Gf2_128) -> Gf2_128 {
    let lo: u64;
    let hi: u64;
    unsafe {
        asm!(
            products_in_registers!(),
            finish_in_registers!(),
            in("d22") x.0 as u64,
            in("d23") (x.0 >> 64) as u64,
            in("d24") y.0 as u64,
            in("d25") (y.0 >> 64) as u64,
            lateout("d0") lo,
            lateout("d1") hi,
            out("d2") _,
            out("d3") _,
            out("d4") _,
            out("d5") _,
            out("d6") _,
            out("d7") _,
            out("d8") _,
            out("d9") _,
            out("d10") _,
            out("d11") _,
            out("d16") _,
            out("d17") _,
            out("d18") _,
            out("d19") _,
            out("d20") _,
            out("d21") _,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    Gf2_128(lo as u128 | ((hi as u128) << 64))
}

#[inline(always)]
pub fn gf2_128_mac(acc: &mut Gf2_128Accum, x: &Gf2_128, y: &Gf2_128) {
    // SAFETY: arm-neon requires NEON. The three complete accumulator elements
    // are read and written in bounds; references cannot alias acc.
    unsafe {
        asm!(
            "vld1.8 {{d22-d23}}, [{x}]",
            "vld1.8 {{d24-d25}}, [{y}]",
            products_in_registers!(),
            "vld1.8 {{d2-d3}}, [{acc}]",
            "veor q4, q4, q1",
            "vst1.8 {{d8-d9}}, [{acc}]!",
            "vld1.8 {{d2-d3}}, [{acc}]",
            "veor q0, q0, q1",
            "vst1.8 {{d0-d1}}, [{acc}]!",
            "vld1.8 {{d2-d3}}, [{acc}]",
            "veor q5, q5, q1",
            "vst1.8 {{d10-d11}}, [{acc}]",
            x = in(reg) x,
            y = in(reg) y,
            acc = inout(reg) acc.0.as_mut_ptr() => _,
            out("d0") _,
            out("d1") _,
            out("d2") _,
            out("d3") _,
            out("d4") _,
            out("d5") _,
            out("d6") _,
            out("d7") _,
            out("d8") _,
            out("d9") _,
            out("d10") _,
            out("d11") _,
            out("d16") _,
            out("d17") _,
            out("d18") _,
            out("d19") _,
            out("d20") _,
            out("d21") _,
            out("d22") _,
            out("d23") _,
            out("d24") _,
            out("d25") _,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(always)]
pub fn gf2_128_accum_reduce(acc: &Gf2_128Accum) -> Gf2_128 {
    let mut result = core::mem::MaybeUninit::<Gf2_128>::uninit();
    // SAFETY: arm-neon requires NEON. The accumulator has three initialized
    // elements, and asm completely initializes the output element.
    unsafe {
        asm!(
            "vld1.8 {{d8-d9}}, [{acc}]!",
            "vld1.8 {{d0-d1}}, [{acc}]!",
            "vld1.8 {{d10-d11}}, [{acc}]",
            finish_in_registers!(),
            "vst1.8 {{d0-d1}}, [{result}]",
            acc = inout(reg) acc.0.as_ptr() => _,
            result = in(reg) result.as_mut_ptr(),
            out("d0") _,
            out("d1") _,
            out("d2") _,
            out("d3") _,
            out("d4") _,
            out("d5") _,
            out("d6") _,
            out("d7") _,
            out("d8") _,
            out("d9") _,
            out("d10") _,
            out("d11") _,
            out("d16") _,
            options(nostack, preserves_flags),
        );
        result.assume_init()
    }
}

#[cfg(test)]
#[path = "../../tests/arm_neon.rs"]
mod tests;
