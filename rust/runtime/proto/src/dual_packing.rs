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

//! Flat hidden-target trace adapter: 127 masked messages in one response.

use std::io::{Error, ErrorKind, Result};

use crate::runtime::algebra::gf2_128::Gf2_128;

pub const DUAL_PACKING_MESSAGES: usize = 127;
pub const DUAL_PACKING_MASK_CELLS: usize = 128;
pub const DUAL_PACKING_PROOF_BYTES: usize = 16 * DUAL_PACKING_MESSAGES;
pub const PACKING_BASIS_ID: u32 = crate::core::algebra::proto::GF2_128_POLYNOMIAL_PACKING_ID as u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DualPacking128Proof {
    pub messages: [Gf2_128; DUAL_PACKING_MESSAGES],
}

impl DualPacking128Proof {
    pub fn write_to_buf(&self, out: &mut Vec<u8>) {
        for value in &self.messages {
            out.extend_from_slice(&value.to_u128().to_le_bytes());
        }
    }

    pub fn read(input: &mut &[u8]) -> Result<Self> {
        if input.len() < DUAL_PACKING_PROOF_BYTES {
            return Err(Error::new(
                ErrorKind::UnexpectedEof,
                "127 flat dual packing messages required",
            ));
        }
        let mut messages = [Gf2_128::default(); DUAL_PACKING_MESSAGES];
        for message in &mut messages {
            *message = Gf2_128::from(u128::from_le_bytes(input[..16].try_into().unwrap()));
            *input = &input[16..];
        }
        Ok(Self { messages })
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != DUAL_PACKING_PROOF_BYTES {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "dual packing proof length mismatch",
            ));
        }
        Self::read(&mut &bytes[..])
    }
}
