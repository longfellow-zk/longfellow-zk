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

//! LFA1/LFA2 format selection for [`CircuitArchive`].

use std::io::BufRead;

use super::{lfa1, lfa2, CircuitArchive, LFA2_MAGIC};

impl CircuitArchive {
    /// Default serialization to LFA2 format.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes_lfa2()
    }

    /// Serializes to LFA2 format (with metadata fields).
    #[must_use]
    pub fn to_bytes_lfa2(&self) -> Vec<u8> {
        lfa2::to_bytes_lfa2(self)
    }

    /// Serializes to LFA1 format (legacy minimal format without header metadata).
    /// Asserts that no metadata information is lost.
    #[must_use]
    pub fn to_bytes_lfa1(&self) -> Vec<u8> {
        lfa1::to_bytes_lfa1(self)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = bytes;
        Self::from_stream(&mut cursor)
    }

    pub fn from_stream<R: BufRead>(stream: &mut R) -> Result<Self, String> {
        let buf = stream
            .fill_buf()
            .map_err(|e| format!("Incomplete header: missing bytes: {e}"))?;

        if buf.starts_with(LFA2_MAGIC) {
            stream.consume(4);
            lfa2::from_stream_lfa2_body(stream)
        } else if !buf.is_empty() && buf[0] == 1 {
            lfa1::from_stream_lfa1(stream)
        } else {
            Err(format!(
                "Unsupported archive header: expected b\"LFA2\" magic or 0x01 (LFA1), got {:?}",
                buf.get(..4)
            ))
        }
    }
}
