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

/// Run compiler/circuit tests through the native LFC3 compiler.
#[cfg(test)]
macro_rules! test_compilers {
    ($path:literal) => {
        mod v2_tests {
            #[allow(dead_code)]
            const V2: bool = true;
            #[allow(unused_imports)]
            use crate::compile::compiler::compile_v2 as compile;
            include!($path);
        }
    };
}

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

#[path = "../util/src/lib.rs"]
pub(crate) mod util;

#[path = "../core"]
pub mod core {
    #[path = "algebra/src/lib.rs"]
    pub mod algebra;
    #[path = "bits/src/lib.rs"]
    pub mod bits;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
}

#[path = "../runtime"]
pub mod runtime {
    #[path = "algebra/src/lib.rs"]
    pub mod algebra;
    #[path = "dual-packing/src/lib.rs"]
    pub mod dual_packing;
    #[path = "ligero/src/lib.rs"]
    pub mod ligero;
    #[path = "merkle/src/lib.rs"]
    pub mod merkle;
    #[path = "polygero/src/lib.rs"]
    pub mod polygero;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
    #[path = "random/src/lib.rs"]
    pub mod random;
    #[path = "sumcheck-v1/src/lib.rs"]
    pub mod sumcheck_v1;
    #[path = "sumcheck-v2/src/lib.rs"]
    pub mod sumcheck_v2;
    #[path = "zk-v1/src/lib.rs"]
    pub mod zk_v1;
    #[path = "zk-v2/src/lib.rs"]
    pub mod zk_v2;
}

cfg_compiler! {
    #[path = "../compile"]
    pub mod compile {
        #[path = "algebra/src/lib.rs"]
        pub mod algebra;
        #[path = "compiler/src/lib.rs"]
        pub mod compiler;
        #[path = "logic/src/lib.rs"]
        pub mod logic;
        #[path = "proto/src/lib.rs"]
        pub mod proto;
        #[path = "polygero/src/lib.rs"]
        pub mod polygero;

        cfg_testonly! {
            #[path = "eval/src/lib.rs"]
            pub mod eval;
        }
    }
}

#[path = "../circuits"]
pub mod circuits {
    #[path = "analog_decoder/src/lib.rs"]
    pub mod analog_decoder;
    #[path = "bit_plucker/src/lib.rs"]
    pub mod bit_plucker;

    cfg_prover_or_compiler! {
        #[path = "ec/src/lib.rs"]
        pub mod ec;
        #[path = "ecdsa2/src/lib.rs"]
        pub mod ecdsa2;
        #[path = "mac/src/lib.rs"]
        pub mod mac;
        #[path = "sha256/src/lib.rs"]
        pub mod sha256;
        #[path = "sha256msg/src/lib.rs"]
        pub mod sha256msg;
    }

    cfg_compiler! {
        #[path = "analog_adder/src/lib.rs"]
        pub mod analog_adder;
        #[path = "arithmetic/src/lib.rs"]
        pub mod arithmetic;
        #[path = "big_bitvec/src/lib.rs"]
        pub mod big_bitvec;
        #[path = "bignum/src/lib.rs"]
        pub mod bignum;
        #[path = "bitvec/src/lib.rs"]
        pub mod bitvec;
        #[path = "boolean/src/lib.rs"]
        pub mod boolean;
        #[path = "gf2_128/src/lib.rs"]
        pub mod gf2_128;
        #[path = "lookup/src/lib.rs"]
        pub mod lookup;
        #[path = "mac_gf128/src/lib.rs"]
        pub mod mac_gf128;
        #[path = "memcmp/src/lib.rs"]
        pub mod memcmp;
        #[path = "polynomial/src/lib.rs"]
        pub mod polynomial;
        #[path = "routing/src/lib.rs"]
        pub mod routing;
    }

    #[cfg(any(
        test,
        feature = "testonly",
        all(
            feature = "experimental",
            any(feature = "compiler", feature = "prover")
        )
    ))]
    #[path = "experimental/src/lib.rs"]
    pub mod experimental;
}

#[cfg(feature = "mdoc")]
#[path = "../applications/mdoc_zk"]
pub mod mdoc {
    #[path = "circuits/src/lib.rs"]
    pub mod circuits;
    #[path = "proto/src/lib.rs"]
    pub mod proto;
    #[path = "runtime/src/lib.rs"]
    pub mod runtime;

    pub use runtime::{find_zk_spec, find_zk_spec_by_hex, v1, v2, ZkSpecRef};

    cfg_compiler! {
        #[path = "artifacts/src/lib.rs"]
        pub mod artifacts;
        #[path = "compile/src/lib.rs"]
        pub mod compile;
        #[path = "development_provider/src/lib.rs"]
        pub mod development_provider;
    }

    cfg_testonly! {
        #[path = "testcases/src/lib.rs"]
        pub mod testcases;
    }
}

/// Checks module dependencies across all source files and inactive feature paths.
#[cfg(test)]
#[path = "dependency_tests.rs"]
mod module_dag_tests;
