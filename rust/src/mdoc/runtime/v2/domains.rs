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

//! The evaluation domains of mdoc's two fields, built in one place for the
//! prover, the verifier, `proof_geometry` and the development provider.

use crate::runtime::algebra::{
    fp2::Fp2Field,
    gf2_128::Gf2_128Field,
    p256::P256Field,
    range_interpolation::{BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory},
    SupportsFFT,
};

/// Call `f` with mdoc's evaluation domains, in `link::composition`'s order:
/// the hash field's, over the full Cantor basis of `gf2`, and the signature
/// field's, the FFT domain of P-256's quadratic extension over `p256`.
pub(in crate::mdoc) fn with_domains<R>(
    gf2: &Gf2_128Field,
    p256: &P256Field,
    f: impl FnOnce(
        (
            &BinaryInterpolatorFactory<'_, Gf2_128Field>,
            &QuadraticExtensionFftInterpolatorFactory<'_, 4, P256Field>,
        ),
    ) -> R,
) -> R {
    let extension = Fp2Field::new(p256);
    let signature = QuadraticExtensionFftInterpolatorFactory::new(
        p256,
        &extension,
        extension.omega(),
        extension.omega_order(),
    );
    f((&BinaryInterpolatorFactory::full_field(gf2), &signature))
}
