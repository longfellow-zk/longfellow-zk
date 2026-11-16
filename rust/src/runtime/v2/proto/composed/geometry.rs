// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The public dimensions of a composed proof.
use crate::runtime::v2::proto::{
    polygero::{PolygeroConfig, PolygeroGeometry},
    zk::CircuitProofGeometry,
};

/// Public dimensions of a composed proof: the host and split circuit
/// geometries and the proof's one Polygero profile, valid for both fields'
/// committed cells; the split circuit has packing degree one (proto I8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedGeometry {
    pub(super) host: CircuitProofGeometry,
    pub(super) split: CircuitProofGeometry,
    pub(super) config: PolygeroConfig,
}
impl ComposedGeometry {
    /// The geometry of a composed proof, if the split circuit has packing
    /// degree one and `config` is a valid Polygero profile for both fields.
    pub fn new(
        host: CircuitProofGeometry,
        split: CircuitProofGeometry,
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
    pub fn host(&self) -> &CircuitProofGeometry {
        &self.host
    }
    pub fn split(&self) -> &CircuitProofGeometry {
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
