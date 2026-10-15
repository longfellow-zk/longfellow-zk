// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0
#[allow(dead_code)]
#[path = "../../../experiments/mldsa/morton.rs"]
mod morton;
use circuits_bitvec::{BitvecIO, BitvecLogic};
use circuits_experimental::mldsa::{
    algebra::CompileFp24Ext6,
    params::{MlDsa44, MlDsa65, MlDsaParams},
    verifier::{MlDsaVerifier, PublicKeyW, SignatureW, VerificationWitness},
};

fn run<P: MlDsaParams>(name: &str) {
    println!(
        "GRID_CONFIG dataset={name} period={} first={} bits={}",
        circuits_experimental::mldsa::shake::slice_period(),
        circuits_experimental::mldsa::shake::first_round_slice() as u8,
        circuits_experimental::mldsa::shake::plucker_bits()
    );
    assert!((1..=6).contains(&circuits_experimental::mldsa::shake::slice_period()));
    let field = CompileFp24Ext6::new();
    let (compiled, _, symbols) = compile_compiler::compile(&field, |logic| {
        let bitvec = BitvecLogic::new(&logic);
        let mut position = compile_logic::K_FIRST_WIRE_POSITION;
        let public_key = PublicKeyW::input::<P>(&logic, &bitvec, &mut position);
        let public_input_count = position;
        let signature = SignatureW::input::<P>(&logic, &bitvec, &mut position);
        let witness = VerificationWitness::input::<P>(&logic, &bitvec, &mut position);
        let byte_io = BitvecIO::new(&bitvec);
        let mu: Vec<_> = (0..64).map(|_| byte_io.next(&mut position)).collect();
        let verifier = MlDsaVerifier::<_, P>::new(&logic);
        (
            verifier.assert_valid_signature_on_mu(&public_key, &signature, &mu, &witness),
            public_input_count,
            position,
        )
    });
    if let Ok(path) = std::env::var("ORDER_EXPORT_CIRCUIT") {
        assert_eq!(compiled.raw.subfield_boundary, compiled.raw.ninput);
        let mut compiled = compiled;
        compiled.raw.layers = compiled
            .raw
            .layers
            .iter()
            .map(compile_compiler::segment_layer)
            .collect();
        let writer = core_proto::writer::CircuitWriter::new(&field, core_proto::FieldID::None);
        println!(
            "EXPORTED_CIRCUIT dataset={name} inputs={} public={} terms={} wires={} layers={} subfield_boundary={}",
            compiled.raw.ninput,
            compiled.raw.npublic_input,
            compiled
                .raw
                .layers
                .iter()
                .map(|l| l.num_terms())
                .sum::<usize>(),
            compiled.raw.noutput + compiled.raw.layers.iter().map(|l| l.nw()).sum::<usize>(),
            compiled.raw.layers.len(),
            compiled.raw.subfield_boundary
        );
        std::fs::write(path, writer.to_bytes_lfc2(&compiled)).unwrap();
    } else {
        morton::core_audit::audit(name, &field, &compiled, &symbols);
    }
}

#[test]
#[ignore = "offline byte ownership and assertion-dependency audit"]
fn mldsa_core_bytes() {
    match std::env::var("ORDER_DATASET").unwrap().as_str() {
        "mldsa44" => run::<MlDsa44>("mldsa44"),
        "mldsa65" => run::<MlDsa65>("mldsa65"),
        _ => panic!("expected mldsa44 or mldsa65"),
    }
}
