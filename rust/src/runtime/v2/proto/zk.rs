// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 proof messages, public geometry and complete-proof encoding.
use crate::{
    core::algebra::{ElementOf, SerializableField},
    runtime::{
        algebra::RuntimeField,
        v2::proto::{
            dual_packing::PackingProof,
            polygero::{
                FieldProof, JointPolygeroProof, PolygeroCommitment, PolygeroConfig,
                PolygeroGeometry,
            },
            sumcheck::{SumcheckProof, SumcheckProofGeometry},
        },
    },
};

cfg_role! {
    mod codec;
}
cfg_prover! {
    mod prover;
}

/// Circuit reduction dimensions, independent of its enclosing participant
/// list: the sumcheck geometry, the packing degree `m >= 1` and the
/// participant's committed cell count `nw`. Its Polygero geometry is derived
/// from `nw` and the enclosing proof geometry's one profile (proto I8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProofGeometry {
    sumcheck: SumcheckProofGeometry,
    packing_degree: usize,
    nw: usize,
}
/// Complete standalone proof geometry: one circuit and the proof's one
/// Polygero profile, valid for the circuit's committed cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProofGeometry {
    circuit: CircuitProofGeometry,
    config: PolygeroConfig,
}
fn invalid_geometry(message: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, message)
}
impl CircuitProofGeometry {
    /// The geometry of a circuit reduction with packing degree
    /// `packing_degree >= 1` whose participant commits `nw` cells.
    pub fn new(
        sumcheck: SumcheckProofGeometry,
        packing_degree: usize,
        nw: usize,
    ) -> std::io::Result<Self> {
        if packing_degree == 0 {
            return Err(invalid_geometry("packing degree zero"));
        }
        Ok(Self {
            sumcheck,
            packing_degree,
            nw,
        })
    }
    pub fn sumcheck(&self) -> &SumcheckProofGeometry {
        &self.sumcheck
    }
    pub fn packing_degree(&self) -> usize {
        self.packing_degree
    }
    /// Committed cells of the participant, its fingerprint masks included.
    pub fn nw(&self) -> usize {
        self.nw
    }
    /// The Polygero geometry of this circuit's cells under `config`, if valid.
    pub(super) fn polygero(&self, config: PolygeroConfig) -> std::io::Result<PolygeroGeometry> {
        PolygeroGeometry::new(self.nw, config)
    }
}
impl ZkProofGeometry {
    /// The geometry of a standalone proof of `circuit` under `config`, if
    /// `config` is a valid Polygero profile for the circuit's cells.
    pub fn new(circuit: CircuitProofGeometry, config: PolygeroConfig) -> std::io::Result<Self> {
        circuit.polygero(config)?;
        Ok(Self { circuit, config })
    }
    pub fn circuit(&self) -> &CircuitProofGeometry {
        &self.circuit
    }
    /// The proof's one Polygero profile.
    pub fn config(&self) -> PolygeroConfig {
        self.config
    }
    /// The circuit's Polygero geometry, derived from its cells and the profile.
    pub fn polygero(&self) -> PolygeroGeometry {
        PolygeroGeometry::validated(self.circuit.nw, self.config)
    }
}
/// A standalone proof; its fields are in send order (proto I4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkProof<const W: usize, F: SerializableField> {
    pub com: PolygeroCommitment,
    pub fingerprints: super::witness_selection::FingerprintResponse<ElementOf<F>>,
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub packing: PackingProof<ElementOf<F>>,
    pub com_proof: JointPolygeroProof<(FieldProof<ElementOf<F>>, ())>,
}
/// A circuit reduction, authenticated later by its participant's shared opening.
/// Only the complete proof readers parse one (proto I2):
///
/// ```compile_fail,E0624
/// use longfellow_zk::runtime::{
///     algebra::gf2_128::Gf2_128Field,
///     v2::proto::{
///         sumcheck::SumcheckProofGeometry,
///         zk::{CircuitProofGeometry, CircuitProof},
///     },
/// };
/// let g = CircuitProofGeometry::new(SumcheckProofGeometry::new(vec![]).unwrap(), 1, 0).unwrap();
/// let _ = CircuitProof::<2, Gf2_128Field>::read(&mut &[][..], &g, &Gf2_128Field::new());
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProof<const W: usize, F: SerializableField> {
    pub sumcheck_proof: SumcheckProof<W, F>,
    pub packing: PackingProof<ElementOf<F>>,
}
impl<const W: usize, F: RuntimeField<W> + SerializableField> CircuitProof<W, F> {
    fn write_parts(
        sumcheck: &SumcheckProof<W, F>,
        packing: &PackingProof<F::E>,
        buf: &mut Vec<u8>,
        g: &CircuitProofGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};
        match packing {
            PackingProof::Direct if g.packing_degree == 1 => {}
            PackingProof::TraceZero { u, .. }
                if g.packing_degree > 1 && u.len() == g.packing_degree => {}
            _ => return Err(Error::new(ErrorKind::InvalidData, "v2 packing shape")),
        }
        sumcheck.write_to_buf(buf, &g.sumcheck, f)?;
        if let PackingProof::TraceZero { u, a } = packing {
            for x in u.iter().chain(std::iter::once(a)) {
                super::util::write_elt_field(buf, x, f);
            }
        }
        Ok(())
    }
    pub fn write_to_buf(
        &self,
        buf: &mut Vec<u8>,
        g: &CircuitProofGeometry,
        f: &F,
    ) -> std::io::Result<()> {
        Self::write_parts(&self.sumcheck_proof, &self.packing, buf, g, f)
    }
}
impl<const W: usize, F: RuntimeField<W> + SerializableField> ZkProof<W, F> {
    pub const MAGIC: [u8; 4] = *b"LFV9";
}

#[cfg(test)]
mod tests;
