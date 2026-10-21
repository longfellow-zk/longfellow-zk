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

use mdoc_zk_proto::mso_attribute::constants::{K_OP_EQ, K_OP_GE, K_OP_LE};

/// Relation a verifier requests between the issuer-signed attribute value and
/// [`RequestedAttribute::cbor_value`].
///
/// `Eq`, `Le` and `Ge` are encoded verbatim into the circuit's 2-bit `op` wire (the
/// discriminants are the `K_OP_*` wire constants). `Pnym` is a request-level marker only:
/// it selects the dedicated pseudonym circuit and is never written to an `op` wire (its
/// numeric value is the reserved operator code that the circuit rejects).
#[repr(u8)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AttributeOp {
    #[default]
    Eq = K_OP_EQ,
    Le = K_OP_LE,
    Ge = K_OP_GE,
    Pnym = 3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestedAttribute {
    pub namespace_id: Vec<u8>,
    pub id: Vec<u8>,
    pub cbor_value: Vec<u8>,
    pub op: AttributeOp,
    pub context: Vec<u8>,
}
