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

use crate::runtime::algebra::SupportsSampling;

/// Trait defining operations for seedable/pseudorandom challenge engines.
pub trait RandomEngine {
    /// Generates raw pseudorandom bytes of the specified length.
    fn bytes(&mut self, len: usize) -> Vec<u8>;

    /// Fill `out` with the next `out.len()` bytes, exactly as `bytes` would
    /// return them. Engines override it to avoid the allocation.
    fn fill(&mut self, out: &mut [u8]) {
        out.copy_from_slice(&self.bytes(out.len()));
    }

    /// Generates a random field element.
    fn elt_field<F: SupportsSampling>(&mut self, f: &F) -> F::E {
        f.sample(|out| self.fill(out))
    }

    /// Generates a slice of field elements with random values.
    fn elt_field_slice<F: SupportsSampling>(&mut self, len: usize, f: &F) -> Vec<F::E> {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(self.elt_field(f));
        }
        v
    }

    /// Generates a random u128.
    fn u128(&mut self) -> u128 {
        let buf = self.bytes(16);
        u128::from_le_bytes(buf.try_into().unwrap())
    }
}

/// The seal of `PrivateRandom`. Only this crate can name it, so only this
/// crate can implement `PrivateRandom`.
pub trait Sealed {}

/// Coins that stay private to the prover: masks, pads, nonces and one-time
/// pads. v2 prover APIs take this, not `RandomEngine`.
///
/// Zero knowledge needs coins that are fresh for every proof and that nobody
/// else can predict: a single proof made with predictable coins reveals the
/// witness. The trait is sealed, so no caller can supply its own engine, such
/// as a public challenge stream, a fixed seed or replayed bytes. Outside this
/// crate only `SecureRandomEngine`, which reads the operating system's CSPRNG
/// for every draw, implements it, and the guarantee holds only in builds
/// without the `testonly` feature: `testonly` also gives it to
/// `DeterministicRng`, a seeded generator for reproducible tests whose proofs
/// reveal their witnesses. The crate's own unit tests use further
/// deterministic engines.
///
/// ```compile_fail,E0277
/// use longfellow_zk::runtime::random::{PrivateRandom, RandomEngine};
/// struct Zeros;
/// impl RandomEngine for Zeros {
///     fn bytes(&mut self, len: usize) -> Vec<u8> {
///         vec![0; len]
///     }
/// }
/// impl PrivateRandom for Zeros {}
/// ```
pub trait PrivateRandom: RandomEngine + Sealed {}
