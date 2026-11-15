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

use crate::core::proto::uleb::read_uleb128;

mod codec;
pub mod lfa1;
pub mod lfa2;

use std::io::BufRead;

use sha2::{Digest, Sha256};

pub const LFA_VERSION: u8 = 1;
pub const LFA2_MAGIC: &[u8; 4] = b"LFA2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchiveEntry {
    pub name: String,
    pub circuit_id: [u8; 32],
    pub payload: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitArchive {
    pub version: u8,
    pub circuit_version: u32,
    pub combined_id: [u8; 32],
    pub created_at: String,
    pub author: String,
    pub generator_tool: String,
    pub description: String,
    pub entries: Vec<ArchiveEntry>,
}

/// Archive metadata and entries; `build` gives each metadata field left
/// `None` its default.
#[derive(Clone, Debug, Default)]
pub struct CircuitArchiveBuilder {
    pub circuit_version: Option<u32>,
    pub created_at: Option<String>,
    pub author: Option<String>,
    pub generator_tool: Option<String>,
    pub description: Option<String>,
    entries: Vec<ArchiveEntry>,
}

impl CircuitArchiveBuilder {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_entry(
        &mut self,
        name: impl Into<String>,
        circuit_id: [u8; 32],
        payload: Vec<u8>,
    ) -> &mut Self {
        self.entries.push(ArchiveEntry {
            name: name.into(),
            circuit_id,
            payload,
        });
        self
    }

    #[must_use]
    pub fn build(self) -> CircuitArchive {
        let combined_id = compute_combined_id(&self.entries);
        let circuit_version = self.circuit_version.unwrap_or(0);
        let created_at = self
            .created_at
            .unwrap_or_else(|| "2026-07-15T00:00:00Z".to_string());
        let author = self.author.unwrap_or_else(|| "Google LLC".to_string());
        let generator_tool = self
            .generator_tool
            .unwrap_or_else(|| "rzkl-compiler v0.1.0".to_string());
        let description = self.description.unwrap_or_default();

        CircuitArchive {
            version: LFA_VERSION,
            circuit_version,
            combined_id,
            created_at,
            author,
            generator_tool,
            description,
            entries: self.entries,
        }
    }
}

pub fn compute_combined_id(entries: &[ArchiveEntry]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for entry in entries {
        hasher.update(entry.circuit_id);
    }
    hasher.finalize().into()
}

impl CircuitArchive {
    #[must_use]
    pub fn builder() -> CircuitArchiveBuilder {
        CircuitArchiveBuilder::new()
    }

    #[must_use]
    pub fn get(&self, name: &str) -> Option<&ArchiveEntry> {
        self.entries.iter().find(|e| e.name == name)
    }
}

pub(in crate::core::proto) fn read_utf8_string<R: BufRead>(
    stream: &mut R,
    max_len: usize,
    field_name: &str,
) -> Result<String, String> {
    let len = read_uleb128(stream)?;
    if len > max_len {
        return Err(format!(
            "Excessive {field_name} string length: {len} > {max_len}"
        ));
    }
    let mut buf = vec![0u8; len];
    stream
        .read_exact(&mut buf)
        .map_err(|_| format!("Incomplete {field_name} string"))?;
    String::from_utf8(buf).map_err(|e| format!("Invalid UTF-8 in {field_name}: {e}"))
}
