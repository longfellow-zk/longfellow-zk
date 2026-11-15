// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The body of a composed proof: a binary host participant and one mixed
//! split participant, opened jointly. Applications wrap it in their own
//! envelope (version and final seal).
//!
//! Fields are encoded in send order (proto I4): the shared root, both
//! fields' fingerprint responses, the split sumcheck, the split message
//! `mu`, the adapter's message, the host sumcheck and packing, both
//! Polygero responses; then the terminal section: both fields' opened rows,
//! the nonces and the frontier, its u64 count first.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::RuntimeField,
        v2::proto::{
            polygero::{
                FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig,
                PolygeroGeometry,
            },
            sumcheck::SumcheckProof,
            witness_selection::{FingerprintResponse, FINGERPRINTS},
            zk::{CircuitGeometry, CircuitProof},
        },
    },
};

/// The adapter's message in a composed proof, with its canonical encoding
/// of exactly `BYTES` bytes. Its reader is sealed: only the crate's
/// complete readers parse it, after the whole proof's length check (proto
/// I2), and no type outside the crate implements it.
pub trait AdapterMessage: sealed::Read {
    const BYTES: usize;
    fn write(&self, out: &mut Vec<u8>);
}
pub(crate) mod sealed {
    /// The adapter message's reader: exactly `AdapterMessage::BYTES` bytes.
    pub trait Read: Sized {
        fn read(b: &mut &[u8]) -> Result<Self, String>;
    }
}

/// Public dimensions of a composed proof: the host and split circuit
/// geometries and the proof's one Polygero profile, valid for both fields'
/// committed cells; the split circuit has packing degree one (proto I8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedGeometry {
    host: CircuitGeometry,
    split: CircuitGeometry,
    config: PolygeroConfig,
}
impl ComposedGeometry {
    /// The geometry of a composed proof, if the split circuit has packing
    /// degree one and `config` is a valid Polygero profile for both fields.
    pub fn new(
        host: CircuitGeometry,
        split: CircuitGeometry,
        config: PolygeroConfig,
    ) -> std::io::Result<Self> {
        if split.packing_degree() != 1 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "split packing degree must be one",
            ));
        }
        host.polygero(config)?;
        split.polygero(config)?;
        Ok(Self {
            host,
            split,
            config,
        })
    }
    pub fn host(&self) -> &CircuitGeometry {
        &self.host
    }
    pub fn split(&self) -> &CircuitGeometry {
        &self.split
    }
    /// The proof's one Polygero profile.
    pub fn config(&self) -> PolygeroConfig {
        self.config
    }
    /// The host's and the split field's Polygero geometries, derived from
    /// their cells and the one profile.
    pub fn polygero(&self) -> [PolygeroGeometry; 2] {
        [&self.host, &self.split].map(|c| PolygeroGeometry::validated(c.nw(), self.config))
    }
}

/// A composed proof body. Only an application's complete reader, which
/// checks the length and the seal, parses one (proto I2):
///
/// ```compile_fail,E0624
/// use longfellow_zk::runtime::{
///     algebra::gf2_128::Gf2_128Field,
///     v2::{
///         foreign::word::MaskedWord,
///         proto::{
///             composed::{ComposedGeometry, ComposedProof},
///             polygero::PolygeroConfig,
///             sumcheck::SumcheckProofGeometry,
///             zk::CircuitGeometry,
///         },
///     },
/// };
/// let c = || CircuitGeometry::new(SumcheckProofGeometry::new(vec![]).unwrap(), 1, 0).unwrap();
/// let config = PolygeroConfig { k: 2, s: 0, n: 4, t: 1 };
/// let g = ComposedGeometry::new(c(), c(), config).unwrap();
/// let f = Gf2_128Field::new();
/// type Body = ComposedProof<2, Gf2_128Field, 2, Gf2_128Field, [MaskedWord<10>; 2]>;
/// let _ = Body::read(&[], &g, &f, &f);
/// ```
///
/// Nor is the adapter message read on its own outside the crate:
///
/// ```compile_fail,E0599
/// use longfellow_zk::runtime::v2::{foreign::word::MaskedWord, proto::composed::AdapterMessage};
/// let mut b: &[u8] = &[0; 4];
/// let _ = <[MaskedWord<10>; 2]>::read(&mut b);
/// ```
///
/// and no type outside the crate is an adapter message:
///
/// ```compile_fail,E0277
/// use longfellow_zk::runtime::v2::proto::composed::AdapterMessage;
/// struct Empty;
/// impl AdapterMessage for Empty {
///     const BYTES: usize = 0;
///     fn write(&self, _: &mut Vec<u8>) {}
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedProof<
    const WH: usize,
    H: SerializableField,
    const WS: usize,
    S: SerializableField,
    M,
> {
    pub commitment: PolygeroCommitment,
    pub fingerprints: (
        FingerprintResponse<ElementOf<H>>,
        (FingerprintResponse<ElementOf<S>>, ()),
    ),
    /// The split frontend's sumcheck; split storage has packing degree one.
    pub split: SumcheckProof<WS, S>,
    /// The split message `mu`.
    pub mu: ElementOf<S>,
    /// The adapter's message.
    pub message: M,
    pub host: CircuitProof<WH, H>,
    pub polygero: JointPolygeroProof<(FieldProof<ElementOf<H>>, (FieldProof<ElementOf<S>>, ()))>,
}
impl<
        const WH: usize,
        H: RuntimeField<WH> + SerializableField,
        const WS: usize,
        S: RuntimeField<WS> + SerializableField,
        M: AdapterMessage,
    > ComposedProof<WH, H, WS, S, M>
{
    /// Bytes of every body field before the frontier and its count (proto
    /// I3); None if they overflow.
    pub fn fixed_len(g: &ComposedGeometry, h: &H, s: &S) -> Option<usize> {
        let (wh, ws) = (h.serialized_size_bytes(), s.serialized_size_bytes());
        let [gh, gs] = g.polygero();
        let [host_response, host_rows] = FieldProof::<()>::wire_lengths(&gh, wh)?;
        let [split_response, split_rows] = FieldProof::<()>::wire_lengths(&gs, ws)?;
        [
            Some(32),
            FINGERPRINTS.checked_mul(wh),
            FINGERPRINTS.checked_mul(ws),
            g.split.proof_len(ws),
            Some(ws),
            Some(M::BYTES),
            g.host.proof_len(wh),
            Some(host_response),
            Some(split_response),
            Some(host_rows),
            Some(split_rows),
            JointPolygeroProof::<()>::fixed_opening_len(g.config.t),
        ]
        .into_iter()
        .try_fold(0usize, |total, x| total.checked_add(x?))
    }
    pub fn write_to_buf(
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
    /// Read exactly the whole body `b`, whose length the complete reader has
    /// checked against `fixed_len` (proto I3): the frontier is its rest.
    /// Crate-private: only an application's complete reader, which checks the
    /// length and the seal, calls it (proto I2).
    #[cfg(any(test, feature = "prover", feature = "verifier"))]
    #[cfg_attr(not(feature = "mdoc"), allow(dead_code))]
    pub(crate) fn read(body: &[u8], g: &ComposedGeometry, h: &H, s: &S) -> Result<Self, String> {
        let mut rest = body;
        let b = &mut rest;
        let commitment = PolygeroCommitment {
            root: super::Digest {
                data: super::util::read_bytes_32(b).map_err(|e| e.to_string())?,
            },
        };
        let fingerprints = (
            FingerprintResponse::read(b, h).map_err(|e| e.to_string())?,
            (
                FingerprintResponse::read(b, s).map_err(|e| e.to_string())?,
                (),
            ),
        );
        let split = SumcheckProof::read(b, g.split.sumcheck(), s).map_err(|e| e.to_string())?;
        let mu = super::read_field(b, s).map_err(|e| e.to_string())?;
        let message = M::read(b)?;
        let host = CircuitProof::read(b, &g.host, h).map_err(|e| e.to_string())?;
        let [gh, gs] = &g.polygero();
        let polygero = JointPolygeroProof::read::<std::io::Error>(
            b,
            g.config.t,
            g.config.n,
            |r| {
                Ok((
                    FieldProof::read_response(r, gh, h)?,
                    (FieldProof::read_response(r, gs, s)?, ()),
                ))
            },
            |bodies, r| {
                bodies.0.read_rows(r, gh, h)?;
                bodies.1 .0.read_rows(r, gs, s)
            },
        )
        .map_err(|e| e.to_string())?;
        Ok(Self {
            commitment,
            fingerprints,
            split,
            mu,
            message,
            host,
            polygero,
        })
    }
}
