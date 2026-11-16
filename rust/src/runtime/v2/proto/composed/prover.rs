// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's encoding of a composed proof body.
use super::{AdapterMessage, ComposedGeometry, ComposedProof};
use crate::{core::algebra::SerializableField, runtime::algebra::RuntimeField};

/// An adapter message the prover writes.
#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
pub(crate) trait WriteAdapterMessage: AdapterMessage {
    fn write(&self, out: &mut Vec<u8>);
}

#[cfg_attr(not(any(test, feature = "mdoc")), allow(dead_code))]
impl<
        const WH: usize,
        H: RuntimeField<WH> + SerializableField,
        const WS: usize,
        S: RuntimeField<WS> + SerializableField,
        M: WriteAdapterMessage,
    > ComposedProof<WH, H, WS, S, M>
{
    pub(crate) fn write_to_buf(
        &self,
        out: &mut Vec<u8>,
        g: &ComposedGeometry,
        h: &H,
        s: &S,
    ) -> Result<(), String> {
        // Emit only bodies the complete reader accepts for `g` (proto I3).
        Self::fixed_len(g, h, s).ok_or("composed proof geometry")?;
        out.extend_from_slice(&self.commitment.root.data);
        self.fingerprints.0.write(out, h);
        self.fingerprints.1 .0.write(out, s);
        self.split
            .write_to_buf(out, g.split.sumcheck(), s)
            .map_err(|e| e.to_string())?;
        out.extend_from_slice(&s.to_bytes(&self.mu));
        self.message.write(out);
        self.host
            .write_to_buf(out, &g.host, h)
            .map_err(|e| e.to_string())?;
        let [gh, gs] = &g.polygero();
        self.polygero
            .write_to_buf::<std::io::Error>(
                out,
                g.config.t,
                g.config.n,
                |b, buf| {
                    b.0.write_response(buf, gh, h)?;
                    b.1 .0.write_response(buf, gs, s)
                },
                |b, buf| {
                    b.0.write_rows(buf, gh, h)?;
                    b.1 .0.write_rows(buf, gs, s)
                },
            )
            .map_err(|e| e.to_string())
    }
}
