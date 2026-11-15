// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Public-key proofs sharing one committed source with a packed Keccak frontend.
cfg_prover! {mod prover;pub(super) use prover::prove;}
cfg_verifier! {mod verifier;pub(super) use verifier::verify;}
