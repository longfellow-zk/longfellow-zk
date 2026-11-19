//! Extract the public challenge schedule from the current mdoc compiler.
use longfellow_zk::{
    mdoc::{
        development_provider::compile_next,
        v2::{decompress_circuits, proof_geometry},
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};

/// The NEXT circuit's per-layer sumcheck schedules.
pub struct Shape {
    pub binary: Vec<usize>,
    pub prime: Vec<usize>,
}

pub fn shape() -> Shape {
    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    let (spec, archive) = compile_next().unwrap().into_parts();
    let (sig, hash) = decompress_circuits(&archive, &prime, &binary).unwrap();
    let geometry = proof_geometry(&spec, &sig, &hash).unwrap();
    Shape {
        binary: geometry.body.host().sumcheck().layers().to_vec(),
        prime: geometry.body.split().sumcheck().layers().to_vec(),
    }
}
