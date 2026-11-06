// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared arithmetic and primitives, with independent protocol implementations.
//! The reexports below preserve existing public paths without duplicating state
//! or giving shared implementations a dependency on either protocol version.

pub mod v1;
pub mod v2;

pub mod algebra {
    #[path = "src/lib.rs"]
    mod shared;
    pub use shared::*;

    // Compatibility exports only; compact-row implementations belong to v1.
    pub use super::v1::subfield_v1;
    pub use super::v1::subfield_v1::SubfieldV1;
    pub mod p256 {
        pub use super::shared::p256::*;
        pub use crate::runtime::v1::subfield_v1::P256SubfieldV1;
    }
    #[cfg(any(test, feature = "tooling"))]
    pub mod fp24_ext6 {
        pub use super::shared::fp24_ext6::*;
        pub use crate::runtime::v1::subfield_v1::RuntimeFp24SubfieldV1;
    }
}

pub mod merkle {
    #[path = "src/lib.rs"]
    mod shared;
    pub use commitment::verify;
    pub use shared::*;

    pub use super::v1::merkle as commitment;
    cfg_prover! { pub use commitment::{commit, open, MerkleCommitment}; }
}

pub mod proto {
    #[path = "src/lib.rs"]
    mod shared;
    pub use shared::*;

    pub use super::{
        v1::proto::{ligero_v1, subfield_v1, sumcheck_v1, zk_v1},
        v2::proto::{dual_packing, polygero, sumcheck_v2, witness_selection, zk_v2},
    };
}

pub mod random {
    #[path = "src/lib.rs"]
    mod shared;
    pub use shared::*;
    pub use transcript_v1::Transcript;

    pub use super::{
        v1::{random as v1, transcript_v1},
        v2::transcript_v2,
    };
}

pub use v1::{ligero_v1, sumcheck_v1, zk_v1};
#[cfg(any(test, feature = "prover", feature = "verifier"))]
pub use v2::witness_selection;
pub use v2::{dual_packing, polygero, sumcheck_v2, zk_v2};
