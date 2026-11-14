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

use std::io::BufRead;

use crate::core::proto::archive::{compute_combined_id, ArchiveEntry, CircuitArchive, LFA_VERSION};

struct Lfa1P256Field;

impl crate::core::algebra::BareField for Lfa1P256Field {
    type E = [u8; 32];
}

impl crate::core::algebra::SerializableField for Lfa1P256Field {
    fn field_id(&self) -> crate::core::algebra::FieldID {
        crate::core::algebra::FieldID::of_prime_field(&self.serialized_mone())
    }
    fn is_binary(&self) -> bool {
        false
    }

    fn serialized_size_bytes(&self) -> usize {
        32
    }

    fn to_bytes_into(&self, e: &Self::E, dst: &mut [u8]) {
        dst[..32].copy_from_slice(e);
    }

    fn bytes_to_element(&self, bytes: &[u8]) -> Result<Self::E, String> {
        let arr: [u8; 32] = bytes
            .try_into()
            .map_err(|_| "invalid P256 element length".to_string())?;
        // P-256 prime modulus in little-endian u64 limbs
        const MODULUS: [u64; 4] = [
            0xffffffffffffffff,
            0x00000000ffffffff,
            0x0000000000000000,
            0xffffffff00000001,
        ];
        let limbs = [
            u64::from_le_bytes(arr[0..8].try_into().unwrap()),
            u64::from_le_bytes(arr[8..16].try_into().unwrap()),
            u64::from_le_bytes(arr[16..24].try_into().unwrap()),
            u64::from_le_bytes(arr[24..32].try_into().unwrap()),
        ];
        if (limbs[3], limbs[2], limbs[1], limbs[0])
            >= (MODULUS[3], MODULUS[2], MODULUS[1], MODULUS[0])
        {
            return Err("P256 element >= modulus".to_string());
        }
        Ok(arr)
    }

    fn serialized_mone(&self) -> Vec<u8> {
        vec![
            0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
            0xff, 0xff, 0xff, 0xff,
        ]
    }
}

/// Reads an LFA1 archive from a stream (concatenated "sig" and "hash" LFC1 circuits starting with
/// version/field byte 1).
pub fn from_stream_lfa1<R: BufRead>(stream: &mut R) -> Result<CircuitArchive, String> {
    let p256 = Lfa1P256Field;
    let gf2 = crate::core::algebra::Gf2_128Field::new();

    let mut raw_bytes = Vec::new();
    stream
        .read_to_end(&mut raw_bytes)
        .map_err(|e| format!("Failed to read LFA1 stream: {e}"))?;

    if raw_bytes.is_empty() || raw_bytes[0] != 1 {
        return Err(format!(
            "Invalid LFA1 header: expected first byte to be 1 (LFC1), got {:?}",
            raw_bytes.first()
        ));
    }

    let cursor1 = &raw_bytes[..];
    let reader_sig =
        crate::core::proto::v1::CircuitReader::new(&p256, crate::core::proto::FieldID::P256);
    let (c_sig, remaining1) = reader_sig.from_bytes(cursor1, false)?;

    let sig_len = raw_bytes.len() - remaining1.len();
    let payload_sig = raw_bytes[..sig_len].to_vec();

    let cursor2 = remaining1;
    let reader_hash =
        crate::core::proto::v1::CircuitReader::new(&gf2, crate::core::proto::FieldID::Gf2_128);
    let (c_hash, remaining2) = reader_hash.from_bytes(cursor2, false)?;

    let hash_len = cursor2.len() - remaining2.len();
    let payload_hash = cursor2[..hash_len].to_vec();

    let entry_sig = ArchiveEntry {
        name: "sig".to_string(),
        circuit_id: c_sig.id,
        payload: payload_sig,
    };

    let entry_hash = ArchiveEntry {
        name: "hash".to_string(),
        circuit_id: c_hash.id,
        payload: payload_hash,
    };

    let entries = vec![entry_sig, entry_hash];
    let combined_id = compute_combined_id(&entries);

    Ok(CircuitArchive {
        version: LFA_VERSION,
        circuit_version: 0,
        combined_id,
        created_at: String::new(),
        author: String::new(),
        generator_tool: String::new(),
        description: String::new(),
        entries,
    })
}
