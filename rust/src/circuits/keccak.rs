// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
cfg_role! { mod concrete; }
cfg_role! { pub use concrete::{keccak_f_1600_trajectory, ConcreteDerived}; }
mod shape;
pub use shape::{ROTC, ROUNDC};
