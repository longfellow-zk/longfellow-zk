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

//! The mdoc document: its parsed form and errors (`parsed`), the device
//! authentication hash both roles compute (`transcript_hash`), and the
//! prover's parser and witness locator (`prover`).
mod parsed;
mod transcript_hash;
pub use parsed::{FieldLocator, MdocParseError, ParsedAttr, ParsedMdoc};
pub use transcript_hash::compute_transcript_hash;

cfg_prover! {
    mod prover;
    pub use prover::parse_mdoc;
    pub(in crate::mdoc) use prover::{map_entry_unique, parse_mdoc_with_mso_check};
}

cfg_testonly! {
    pub(crate) use prover::format_cose_sign1_message;
}

#[cfg(test)]
mod tests;
