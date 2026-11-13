// Extract the public challenge schedule from the current mdoc compiler.
use longfellow_zk::{
    mdoc::{
        development_provider::compile_next,
        v2::{decompress_circuits, proof_geometry},
    },
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
fn main() {
    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    for attributes in 1..=4 {
        let (spec, archive) = compile_next(attributes).unwrap().into_parts();
        let (sig, hash) = decompress_circuits(&archive, &prime, &binary).unwrap();
        let geometry = proof_geometry(&spec, &sig, &hash).unwrap();
        let binary_rounds = geometry.body.host.sc_geom.logw_layers;
        let prime_rounds = geometry.body.split.sc_geom.logw_layers;
        println!(
            "{{\"attributes\":{},\"binary_rounds\":{:?},\"prime_rounds\":{:?}}}",
            attributes, binary_rounds, prime_rounds
        );
    }
}
