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

//! Interpolate between contiguous ranges of a fixed, implicit point table.
//!
//! A source of length `k > 0` specifies the unique polynomial of degree `< k`.
//! Destination ranges may precede, follow, or overlap the source, and may have
//! any length, including zero. Ranges describe point indices, not memory aliases.
//! Plans contain public preprocessing only and may be reused for different rows.
//! Each application returns its encoded vector and allocates temporary work locally.

//!
//! ```
//! use longfellow_zk::runtime::algebra::{
//!     fp2::Fp2Field,
//!     p256::P256Field,
//!     range_interpolation::{
//!         InterpolationPlan, QuadraticExtensionFftInterpolatorFactory, RangeInterpolatorFactory,
//!     },
//!     SupportsFFT,
//! };
//! use longfellow_zk::core::algebra::AlgebraicField;
//!
//! let field = P256Field::new();
//! let extension = Fp2Field::new(&field);
//! let domain = QuadraticExtensionFftInterpolatorFactory::new(
//!     &field, &extension, extension.omega(), extension.omega_order(),
//! );
//! let plan = domain.make_range(5..8, 0..12);
//! let output = plan.apply(&vec![field.one(); 3]);
//! assert_eq!(output, vec![field.one(); 12]);
//! ```

use super::RuntimeField;

mod arithmetic;
pub(in crate::runtime) mod binary;
mod domain;
pub(in crate::runtime) mod quadratic_extension_fft;
pub(in crate::runtime) mod scalar;
pub use binary::{BinaryInterpolationPlan, BinaryInterpolatorFactory};
use domain::{difference, Ranges};
pub use domain::{
    interpolate_range, EvaluationDomain, InterpolationPlan, RangeInterpolatorFactory,
};
pub use quadratic_extension_fft::{
    QuadraticExtensionFftInterpolationPlan, QuadraticExtensionFftInterpolatorFactory,
};
pub use scalar::{ScalarInterpolationPlan, ScalarInterpolatorFactory};

pub(super) use super::field::batch_inverse;
