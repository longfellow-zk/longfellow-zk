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

//! Longfellow v2 application error.

// Return codes for the run_mdoc_prover method. Each value is the C library's
// code; the codes v2 never returns have no variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MdocProverErrorCode {
    InvalidInput = 2,
    CircuitParsingFailure = 3,
    HashParsingFailure = 4,
    WitnessCreationFailure = 5,
    GeneralFailure = 6,
    InvalidZkSpecVersion = 8,
    NamespacesMissing = 17,
    MsoDecodingFailure = 22,
    AttributeNotFound = 31,
    AttributeTooLong = 32,
    TaggedMsoTooBig = 33,
    UnsupportedAttribute = 36,
}

// Return codes for the run_mdoc_verifier method, likewise the C library's
// codes without the ones v2 never returns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MdocVerifierErrorCode {
    CircuitParsingFailure = 1,
    HashParsingFailure = 3,
    GeneralFailure = 5,
    InvalidInput = 7,
    AttributeNumberMismatch = 9,
    InvalidZkSpecVersion = 10,
    UnsupportedAttribute = 11,
}
