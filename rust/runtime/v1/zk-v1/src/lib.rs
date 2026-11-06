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

//! Legacy v1 zero-knowledge system: affine sumcheck backed by Ligero.
//!
//! The prover commits private inputs and sumcheck pads before proving the circuit.
//! The verifier reconstructs constraints on those hidden values and checks them
//! with Ligero. Both roles use `constraint_compiler` to map symbolic pad references
//! and public inputs to commitment coordinates. Prover and verifier orchestration
//! remain in separate, feature-gated modules.

pub mod common;
pub mod constraint_compiler;

pub use crate::runtime::proto::zk_v1::ZkProof;

cfg_prover! {
    pub mod prover;
    pub use prover::ZkProver;
}

cfg_verifier! {
    pub mod verifier;
    pub use verifier::ZkVerifier;
}

#[cfg(test)]
#[path = "../tests/zk.rs"]
mod tests_zk;
