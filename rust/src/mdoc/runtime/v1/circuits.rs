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

//! Longfellow v1 circuit archive decoding.

use std::io::BufRead;

pub fn decompress_circuits(
    compressed: &[u8],
    p256: &crate::runtime::algebra::p256::P256Field,
    gf2: &crate::runtime::algebra::gf2_128::Gf2_128Field,
) -> Result<
    (
        crate::core::proto::v1::Circuit<crate::runtime::algebra::p256::P256Field>,
        crate::core::proto::v1::Circuit<crate::runtime::algebra::gf2_128::Gf2_128Field>,
    ),
    String,
> {
    let zstd_decoder = zstd::stream::read::Decoder::new(compressed)
        .map_err(|e| format!("Failed to initialize zstd decoder: {e}"))?;
    let mut buf_stream = std::io::BufReader::new(zstd_decoder);

    let is_lfa2 = {
        let peek = buf_stream
            .fill_buf()
            .map_err(|e| format!("Failed to read circuit header: {e}"))?;
        peek.starts_with(crate::core::proto::archive::LFA2_MAGIC)
    };

    if is_lfa2 {
        let archive = crate::core::proto::archive::CircuitArchive::from_stream(&mut buf_stream)?;

        let sig_entry = archive
            .get("sig")
            .ok_or_else(|| "Missing 'sig' entry in circuit archive".to_string())?;
        let reader_sig =
            crate::core::proto::v1::CircuitReader::new(p256, crate::core::proto::FieldID::P256);
        let (c_sig, _) = reader_sig.from_bytes(&sig_entry.payload, false)?;

        let hash_entry = archive
            .get("hash")
            .ok_or_else(|| "Missing 'hash' entry in circuit archive".to_string())?;
        let reader_hash =
            crate::core::proto::v1::CircuitReader::new(gf2, crate::core::proto::FieldID::Gf2_128);
        let (c_hash, _) = reader_hash.from_bytes(&hash_entry.payload, false)?;

        Ok((c_sig, c_hash))
    } else {
        let reader1 =
            crate::core::proto::v1::CircuitReader::new(p256, crate::core::proto::FieldID::P256);
        let c_sig = reader1.from_stream(&mut buf_stream, false)?;

        let reader2 =
            crate::core::proto::v1::CircuitReader::new(gf2, crate::core::proto::FieldID::Gf2_128);
        let c_hash = reader2.from_stream(&mut buf_stream, false)?;

        Ok((c_sig, c_hash))
    }
}
