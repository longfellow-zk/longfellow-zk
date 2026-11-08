#![deny(unreachable_pub, private_interfaces)]
// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Shared arithmetic and primitives, with independent protocol implementations.
//! The reexports below preserve public v1 paths without duplicating state
//! or giving shared implementations a dependency on either protocol version.

pub mod v1;
pub mod v2;

pub mod algebra {
    #[path = "src/lib.rs"]
    mod shared;
    pub use shared::*;

    // Compatibility exports only; compact-row implementations belong to v1.
    pub use super::v1::subfield as subfield_v1;
    pub use super::v1::subfield::SubfieldV1;
    pub mod p256 {
        pub use super::shared::p256::*;
        pub use crate::runtime::v1::subfield::P256SubfieldV1;
    }
    #[cfg(any(test, feature = "tooling"))]
    pub mod fp24_ext6 {
        pub use super::shared::fp24_ext6::*;
        pub use crate::runtime::v1::subfield::RuntimeFp24SubfieldV1;
    }
}

/// Legacy Merkle paths retain the deployed implementation and types.
pub mod merkle {
    pub use super::v1::merkle::*;
}

/// Legacy proof paths retain the deployed wire encoding.
pub mod proto {
    pub use super::v1::proto::{
        ligero as ligero_v1, merkle, subfield as subfield_v1, sumcheck as sumcheck_v1, util,
        zk as zk_v1, Digest, MerkleNonce, MerkleProof, DIGEST_LEN, NONCE_LEN,
    };
}

pub mod random {
    #[path = "src/lib.rs"]
    mod shared;
    pub use shared::*;
    pub use transcript_v1::Transcript;

    pub use super::v1::{random as v1, transcript as transcript_v1};
}

pub use v1::{ligero as ligero_v1, sumcheck as sumcheck_v1, zk as zk_v1};
