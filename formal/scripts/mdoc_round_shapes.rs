// Extract the public challenge schedule from the current mdoc compiler.
use longfellow_zk::{
    mdoc::{development_provider::compile_next, v2::decompress_circuits},
    runtime::algebra::{gf2_128::Gf2_128Field, p256::P256Field},
};
fn main() {
    let binary = Gf2_128Field::new();
    let prime = P256Field::new();
    for attributes in 1..=4 {
        let (_, archive) = compile_next(attributes).unwrap().into_parts();
        let (sig, hash) = decompress_circuits(&archive, &prime, &binary, false).unwrap();
        let binary_rounds: Vec<_> = hash.raw.layers.iter().map(|l| l.logw()).collect();
        let prime_rounds: Vec<_> = sig.raw.layers.iter().map(|l| l.logw()).collect();
        println!("{{\"attributes\":{},\"binary_rounds\":{:?},\"prime_rounds\":{:?}}}",
            attributes, binary_rounds, prime_rounds);
    }
}
