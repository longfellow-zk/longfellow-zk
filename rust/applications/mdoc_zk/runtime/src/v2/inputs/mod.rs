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

//! Longfellow v2 public inputs and private witness encoding.

mod builder;
mod public;
pub(super) use public::{public_inputs_fit, push_input_hash, push_input_sig};

cfg_prover! {
    mod private;
    pub(super) use private::{push_witness_hash, push_witness_sig};
}

#[cfg(test)]
#[path = "../../../tests/v2_inputs.rs"]
mod tests;

#[cfg(all(feature = "experimental", any(test, feature = "prover")))]
pub(super) use private::push_witness_hash_boolean;
#[cfg(feature = "experimental")]
pub(super) use public::push_input_hash_boolean;
