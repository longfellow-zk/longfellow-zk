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

// Keep branch-free integer operations on ARM in both field backends.
// LLVM can turn the generic Rust conditional move into a secret-dependent
// early return, even when its source is written as a bit-mask selection.
use core::arch::asm;

#[cfg(feature = "arm-neon")]
#[path = "arm_neon.rs"]
mod neon;
#[cfg(feature = "arm-neon")]
pub use neon::{gf2_128_accum_reduce, gf2_128_mac, gf2_128_mul, Gf2_128, Gf2_128Accum};

#[cfg(not(feature = "arm-neon"))]
#[path = "generic.rs"]
mod scalar;
#[cfg(not(feature = "arm-neon"))]
pub use scalar::{gf2_128_accum_reduce, gf2_128_mac, gf2_128_mul, Gf2_128, Gf2_128Accum};

/// Register-only conditional selection keeps LLVM from introducing a
/// conditional branch around the modular-reduction result.
#[inline(always)]
pub fn cmovne<const N: usize>(
    a: &mut [crate::runtime::algebra::limb::Limb; N],
    x: crate::runtime::algebra::limb::Limb,
    y: crate::runtime::algebra::limb::Limb,
    b: &[crate::runtime::algebra::limb::Limb; N],
) {
    let nz = x ^ y;
    for i in 0..N {
        let mut value = a[i];
        // SAFETY: all operands are integers. CMP and MOVNE touch no memory
        // and select b[i] exactly when x != y. Flags are declared clobbered.
        unsafe {
            asm!(
                "cmp {nz}, #0",
                // Required in Thumb-2; the assembler emits nothing for IT
                // in ARM mode. MOVNE leaves the comparison flags untouched.
                "it ne",
                "movne {value}, {replacement}",
                nz = in(reg) nz,
                value = inout(reg) value,
                replacement = in(reg) b[i],
                options(pure, nomem, nostack),
            );
        }
        a[i] = value;
    }
}

#[inline(always)]
pub fn cmovnz<const N: usize>(
    a: &mut [crate::runtime::algebra::limb::Limb; N],
    nz: crate::runtime::algebra::limb::Limb,
    b: &[crate::runtime::algebra::limb::Limb; N],
) {
    cmovne(a, nz, 0, b);
}
pub use cmovnz as cmovzn;

/// Keep zero opaque to LLVM so carry propagation can use ADC chains.
#[inline(always)]
pub fn zero_but_you_dont_know_it() -> crate::runtime::algebra::limb::Limb {
    let mut zero = 0u32;
    // SAFETY: this empty identity operation preserves the value and flags,
    // has no memory effects, and prevents folding the input into a constant.
    unsafe {
        asm!(
            "/* {zero} */",
            zero = inout(reg) zero,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    zero
}
