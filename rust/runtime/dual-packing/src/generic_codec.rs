// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Canonical generic proof envelope, bound to trusted extension parameters.
use super::generic::PackingProof;
use crate::{
    core::algebra::SerializableField,
    runtime::algebra::packing::{AmbientElement, PackingExtension, PackingParameters},
};
impl<E: Clone> PackingProof<E> {
    pub fn write<X: PackingExtension>(&self, p: &PackingParameters<X>) -> Result<Vec<u8>, String>
    where X::Ambient: SerializableField<E = E> {
        match self {
            Self::Direct if p.degree() == 1 => Ok(Vec::new()),
            Self::TraceZero { u, a } if p.degree() > 1 && u.len() == p.degree() => {
                let mut bytes = Vec::new();
                if !p.binary128_profile() {
                    let descriptor = p.descriptor();
                    bytes.extend_from_slice(b"LPK1");
                    bytes.extend_from_slice(&(descriptor.len() as u64).to_le_bytes());
                    bytes.extend_from_slice(&descriptor);
                }
                for x in u.iter().chain(std::iter::once(a)) {
                    bytes.extend_from_slice(&p.field().to_bytes(x));
                }
                Ok(bytes)
            }
            _ => Err("packing proof shape".into()),
        }
    }
}
impl<X: PackingExtension> PackingParameters<X>
where X::Ambient: SerializableField
{
    pub fn read_proof(&self, bytes: &mut &[u8]) -> Result<PackingProof<AmbientElement<X>>, String> {
        if self.degree() == 1 {
            return Ok(PackingProof::Direct);
        }
        let descriptor = self.descriptor();
        let legacy = self.binary128_profile();
        let header = if legacy {
            0
        } else {
            12usize
                .checked_add(descriptor.len())
                .ok_or("packing codec overflow")?
        };
        let width = self.field().serialized_size_bytes();
        if width == 0 {
            return Err("packing field width".into());
        }
        let count = self
            .degree()
            .checked_add(1)
            .ok_or("packing codec overflow")?;
        let end = count
            .checked_mul(width)
            .and_then(|n| n.checked_add(header))
            .ok_or("packing codec overflow")?;
        let b = bytes.get(..end).ok_or("truncated packing proof")?;
        if !legacy
            && (&b[..4] != b"LPK1"
                || b[4..12] != (descriptor.len() as u64).to_le_bytes()
                || b[12..header] != descriptor)
        {
            return Err("packing descriptor mismatch".into());
        }
        let mut fields = b[header..]
            .chunks_exact(width)
            .map(|raw| {
                let x = self.field().bytes_to_element(raw)?;
                if self.field().to_bytes(&x) != raw {
                    return Err("noncanonical packing field element".into());
                }
                Ok(x)
            })
            .collect::<Result<Vec<_>, String>>()?;
        let a = fields.pop().unwrap();
        *bytes = &bytes[end..];
        Ok(PackingProof::TraceZero { u: fields, a })
    }
}
