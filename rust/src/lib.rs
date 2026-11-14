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

#![deny(unreachable_pub)]
#![deny(unused_imports)]

/// Conditionally includes items when `feature = "compiler"` (or `test`) is active.
macro_rules! cfg_compiler {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "compiler"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "prover"` (or `test`) is active.
macro_rules! cfg_prover {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "prover"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "verifier"` (or `test`) is active.
macro_rules! cfg_verifier {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "verifier"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "prover"` or `feature = "compiler"` (or `test`) is
/// active.
macro_rules! cfg_prover_or_compiler {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "prover", feature = "compiler"))]
            $item
        )*
    };
}

/// Conditionally includes items when `feature = "testonly"` (or `test`) is active.
macro_rules! cfg_testonly {
    ($($item:item)*) => {
        $(
            #[cfg(any(test, feature = "testonly"))]
            $item
        )*
    };
}

pub(crate) mod util;

pub mod core {
    pub mod algebra;
    pub mod bits;
    pub mod proto;
}

pub mod runtime;

cfg_compiler! {
    pub mod compile {
        pub mod algebra;
        pub mod compiler;
        pub mod debug;
        pub mod logic;
    }
}

pub mod circuits {
    pub mod analog_decoder;
    cfg_prover_or_compiler! {
        pub mod ec;
        pub mod ecdsa2;
        pub mod sha256;
        pub mod sha256msg;
    }
    cfg_compiler! {
        pub mod analog_adder;
        pub mod arithmetic;
        pub mod big_bitvec;
        pub mod bignum;
        pub mod bitvec;
        pub mod boolean;
        pub mod gf2_128;
        pub mod lookup;
        pub mod memcmp;
        pub mod polynomial;
        pub mod routing;
    }
}

#[cfg(feature = "mdoc")]
pub mod mdoc {
    pub mod circuits;
    pub mod proto;
    mod runtime;

    #[cfg(feature = "v1")]
    pub use runtime::v1;
    #[cfg(feature = "v1")]
    pub use runtime::LONGFELLOW_V1;
    pub use runtime::{find_zk_spec, find_zk_spec_by_hex, v2, ZkSpecRef, LONGFELLOW_V2};

    cfg_compiler! {
        pub mod artifacts;
        pub mod compile;
        pub mod development_provider;
    }
    cfg_testonly! {
        pub mod testcases;
    }
}
