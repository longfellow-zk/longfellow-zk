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

use super::*;
use crate::runtime::algebra::arch::{
    cmovne,
    tests::{next, reference_mul},
    zero_but_you_dont_know_it,
};

// Independent unreduced polynomial product; no Karatsuba or byte shuffles.
fn polynomial_mul(x: u64, y: u64) -> u128 {
    let mut product = 0;
    for bit in 0..64 {
        if (y >> bit) & 1 != 0 {
            product ^= (x as u128) << bit;
        }
    }
    product
}

fn reference_coefficients(x: u128, y: u128) -> [u128; 3] {
    let (xl, xh) = (x as u64, (x >> 64) as u64);
    let (yl, yh) = (y as u64, (y >> 64) as u64);
    [
        polynomial_mul(xl, yl),
        polynomial_mul(xl ^ xh, yl ^ yh),
        polynomial_mul(xh, yh),
    ]
}

// Polynomial long division of all 256 bits. In particular, this does not
// reuse the implementation's two X^64 folds or its bytewise 0x87 multiply.
fn reference_reduce(acc: &Gf2_128Accum) -> u128 {
    let [t0, t1, t2] = acc.0.map(|x| x.0);
    let cross = t0 ^ t1 ^ t2;
    let mut words = [
        t0 as u64,
        ((t0 >> 64) as u64) ^ (cross as u64),
        (t2 as u64) ^ ((cross >> 64) as u64),
        (t2 >> 64) as u64,
    ];
    for bit in (128..256).rev() {
        if (words[bit / 64] >> (bit % 64)) & 1 != 0 {
            for offset in [0, 1, 2, 7, 128] {
                let index = bit - 128 + offset;
                words[index / 64] ^= 1 << (index % 64);
            }
        }
    }
    assert_eq!(&words[2..], &[0, 0]);
    words[0] as u128 | ((words[1] as u128) << 64)
}

#[test]
fn raw_products_all_basis_pairs() {
    // Nonzero seeds also detect overwrites in place of XOR accumulation.
    let seed = [u128::MAX, 0x0123456789abcdef_fedcba9876543210, 1 << 127];
    for i in 0..128 {
        for j in 0..128 {
            let (x, y) = (Gf2_128(1 << i), Gf2_128(1 << j));
            let products = reference_coefficients(x.0, y.0);
            let expected = core::array::from_fn(|k| Gf2_128(seed[k] ^ products[k]));
            let mut acc = Gf2_128Accum(seed.map(Gf2_128));
            gf2_128_mac(&mut acc, &x, &y);
            assert_eq!(acc.0, expected, "raw bits {i}, {j}");
            assert_eq!(gf2_128_accum_reduce(&acc).0, reference_reduce(&acc));
            gf2_128_mac(&mut acc, &x, &y);
            assert_eq!(acc.0, seed.map(Gf2_128), "cancel bits {i}, {j}");
        }
    }
}

#[test]
fn reduction_all_384_basis_bits_and_dense_coefficients() {
    for slot in 0..3 {
        for bit in 0..128 {
            let mut acc = Gf2_128Accum::default();
            acc.0[slot] = Gf2_128(1 << bit);
            assert_eq!(
                gf2_128_accum_reduce(&acc).0,
                reference_reduce(&acc),
                "slot {slot}, bit {bit}"
            );
        }
    }
    let mut state = 0x1a2b3c4d5e6f7788_99aabbccddeeff00;
    for i in 0..4096 {
        let acc = if i == 0 {
            Gf2_128Accum([Gf2_128(u128::MAX); 3])
        } else {
            Gf2_128Accum(core::array::from_fn(|_| Gf2_128(next(&mut state))))
        };
        let saved = acc;
        assert_eq!(
            gf2_128_accum_reduce(&acc).0,
            reference_reduce(&acc),
            "dense case {i}"
        );
        assert_eq!(acc, saved, "reduction must not modify the accumulator");
    }
}

#[test]
fn raw_dense_accumulation_and_reuse() {
    let mut state = 0xdeadbeef12345678_abcdef9876543210;
    let mut acc = Gf2_128Accum([Gf2_128(u128::MAX); 3]);
    let mut expected = [u128::MAX; 3];
    for i in 0..4096 {
        let (x, y) = (Gf2_128(next(&mut state)), Gf2_128(next(&mut state)));
        let products = reference_coefficients(x.0, y.0);
        for k in 0..3 {
            expected[k] ^= products[k];
        }
        gf2_128_mac(&mut acc, &x, &y);
        assert_eq!(acc.0, expected.map(Gf2_128), "dense raw case {i}");
        assert_eq!(gf2_128_accum_reduce(&acc).0, reference_reduce(&acc));
        assert_eq!(gf2_128_mul(x, y).0, reference_mul(x.0, y.0));
    }
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Guarded<T> {
    before: [u64; 3],
    value: T,
    after: [u64; 3],
}

impl<T> Guarded<T> {
    fn new(value: T) -> Self {
        Self {
            before: [0x0123456789abcdef; 3],
            value,
            after: [0xfedcba9876543210; 3],
        }
    }
}

#[test]
fn natural_alignment_and_memory_canaries() {
    // ARMv7 u128 needs 8-byte, not 16-byte, alignment. These addresses are
    // deliberately 8 modulo 16, while remaining valid Rust references.
    assert_eq!(core::mem::align_of::<Gf2_128>(), 8);
    let x = Guarded::new(Gf2_128(0x0102030405060708_090a0b0c0d0e0f10));
    let y = Guarded::new(Gf2_128(u128::MAX));
    let mut acc = Guarded::new(Gf2_128Accum([Gf2_128(u128::MAX); 3]));
    assert_eq!((&x.value as *const _ as usize) % 16, 8);
    assert_eq!((&y.value as *const _ as usize) % 16, 8);
    assert_eq!((&acc.value as *const _ as usize) % 16, 8);
    let (saved_x, saved_y, saved_acc) = (x, y, acc);
    gf2_128_mac(&mut acc.value, &x.value, &y.value);
    assert_eq!(x, saved_x);
    assert_eq!(y, saved_y);
    assert_eq!(acc.before, saved_acc.before);
    assert_eq!(acc.after, saved_acc.after);
    assert_eq!(
        gf2_128_accum_reduce(&acc.value).0,
        reference_reduce(&acc.value)
    );
    // Shared inputs are legal, unlike aliasing either input with &mut acc.
    gf2_128_mac(&mut acc.value, &x.value, &x.value);
    assert_eq!(
        gf2_128_accum_reduce(&acc.value).0,
        reference_reduce(&acc.value)
    );
    assert_eq!(acc.before, saved_acc.before);
    assert_eq!(acc.after, saved_acc.after);
}

mod guarded_pages {
    use core::ffi::{c_int, c_void};

    use super::*;

    unsafe extern "C" {
        fn getpagesize() -> c_int;
        fn mmap64(
            addr: *mut c_void,
            len: usize,
            prot: c_int,
            flags: c_int,
            fd: c_int,
            offset: i64,
        ) -> *mut c_void;
        fn mprotect(addr: *mut c_void, len: usize, prot: c_int) -> c_int;
        fn munmap(addr: *mut c_void, len: usize) -> c_int;
    }

    struct Page<T> {
        mapping: *mut c_void,
        len: usize,
        value: *mut T,
    }

    impl<T> Page<T> {
        fn new(value: T, at_end: bool) -> Self {
            // Linux ARM constants: PROT_NONE=0, READ|WRITE=3,
            // MAP_PRIVATE|MAP_ANONYMOUS=0x22. Both neighboring pages fault.
            unsafe {
                let page = getpagesize() as usize;
                assert!(page.is_power_of_two());
                assert!(core::mem::size_of::<T>() <= page);
                assert!(core::mem::align_of::<T>() <= page);
                // Use the explicit 64-bit offset ABI on both glibc and musl.
                let mapping = mmap64(core::ptr::null_mut(), 3 * page, 0, 0x22, -1, 0);
                assert_ne!(
                    mapping as isize,
                    -1,
                    "mmap: {}",
                    std::io::Error::last_os_error()
                );
                let data = mapping.cast::<u8>().add(page);
                if mprotect(data.cast(), page, 3) != 0 {
                    munmap(mapping, 3 * page);
                    panic!("mprotect failed");
                }
                let offset = if at_end {
                    page - core::mem::size_of::<T>()
                } else {
                    0
                };
                let slot = data.add(offset).cast::<T>();
                slot.write(value);
                Self {
                    mapping,
                    len: 3 * page,
                    value: slot,
                }
            }
        }

        fn get(&self) -> &T {
            // SAFETY: the slot is initialized, aligned, mapped and owned.
            unsafe { &*self.value }
        }

        fn get_mut(&mut self) -> &mut T {
            // SAFETY: exclusive access to this owned, initialized slot.
            unsafe { &mut *self.value }
        }
    }

    impl<T> Drop for Page<T> {
        fn drop(&mut self) {
            unsafe {
                self.value.drop_in_place();
                assert_eq!(munmap(self.mapping, self.len), 0);
            }
        }
    }

    #[test]
    fn no_reads_or_writes_past_object_boundaries() {
        for x_end in [false, true] {
            for y_end in [false, true] {
                for acc_end in [false, true] {
                    let x = Page::new(Gf2_128(u128::MAX), x_end);
                    let y = Page::new(Gf2_128(0x0123456789abcdef_fedcba9876543210), y_end);
                    let mut acc = Page::new(Gf2_128Accum::default(), acc_end);
                    let expected = reference_mul(x.get().0, y.get().0);
                    gf2_128_mac(acc.get_mut(), x.get(), y.get());
                    assert_eq!(gf2_128_accum_reduce(acc.get()).0, expected);
                    assert_eq!(gf2_128_mul(*x.get(), *y.get()).0, expected);
                    assert_eq!(x.get().0, u128::MAX);
                    assert_eq!(y.get().0, 0x0123456789abcdef_fedcba9876543210);
                }
            }
        }
    }
}

struct Probe {
    x: Gf2_128,
    y: Gf2_128,
    acc: Gf2_128Accum,
    product: Gf2_128,
    reduced: Gf2_128,
    selected: [u32; 4],
    zero: u32,
}

#[inline(never)]
unsafe extern "C" fn abi_probe(context: *mut Probe) {
    // SAFETY: the test passes exclusive access to an initialized Probe.
    let p = unsafe { &mut *context };
    p.product = gf2_128_mul(p.x, p.y);
    gf2_128_mac(&mut p.acc, &p.x, &p.y);
    p.reduced = gf2_128_accum_reduce(&p.acc);
    cmovne(&mut p.selected, p.x.0 as u32, p.y.0 as u32, &[1, 2, 3, 4]);
    p.zero = zero_but_you_dont_know_it();
}

#[test]
fn callee_saved_vfp_registers_survive() {
    let expected: [u64; 8] = [
        0x0000000000000000,
        0xffffffffffffffff,
        0x0123456789abcdef,
        0xfedcba9876543210,
        0x5555555555555555,
        0xaaaaaaaaaaaaaaaa,
        0x8000000000000001,
        0x7ff8123456789abc,
    ];
    let mut registers = expected;
    let mut p = Probe {
        x: Gf2_128(0xfedcba9876543210_0123456789abcdef),
        y: Gf2_128(u128::MAX),
        acc: Gf2_128Accum::default(),
        product: Gf2_128(0),
        reduced: Gf2_128(0),
        selected: [0; 4],
        zero: u32::MAX,
    };
    // Load bit patterns into every callee-saved VFP register, call the real
    // backend through the C ABI, and inspect them before Rust can reuse them.
    // The block itself declares its d8-d15 writes and all C caller clobbers.
    // r4 holds the buffer across the call and is also callee-saved by AAPCS32.
    unsafe {
        asm!(
            "vldmia r4, {{d8-d15}}",
            "bl {probe}",
            "vstmia r4, {{d8-d15}}",
            probe = sym abi_probe,
            in("r0") &mut p,
            in("r4") registers.as_mut_ptr(),
            out("d8") _, out("d9") _, out("d10") _, out("d11") _,
            out("d12") _, out("d13") _, out("d14") _, out("d15") _,
            clobber_abi("C"),
        );
    }
    assert_eq!(registers, expected);
    assert_eq!(p.product.0, reference_mul(p.x.0, p.y.0));
    assert_eq!(p.reduced, p.product);
    assert_eq!(p.selected, [1, 2, 3, 4]);
    assert_eq!(p.zero, 0);
}
