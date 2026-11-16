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

use crate::mdoc::proto::hash::constants::{K_COSE1_PREFIX, K_COSE1_PREFIX_LEN};

pub const K_DEVICE_AUTHENTICATION_HEADER: [u8; 22] = [
    0x84, 0x74, b'D', b'e', b'v', b'i', b'c', b'e', b'A', b'u', b't', b'h', b'e', b'n', b't', b'i',
    b'c', b'a', b't', b'i', b'o', b'n',
];

/// The COSE Sig_structure header: the hashed preimage's COSE prefix without its
/// final byte-string tag, which the signed payload supplies.
pub const K_COSE_SIGN1_SIGNING_HEADER: [u8; K_COSE1_PREFIX_LEN - 1] = {
    let mut header = [0; K_COSE1_PREFIX_LEN - 1];
    let mut i = 0;
    while i < header.len() {
        header[i] = K_COSE1_PREFIX[i];
        i += 1;
    }
    header
};

pub const K_TAG24: [u8; 2] = [0xD8, 0x18];
