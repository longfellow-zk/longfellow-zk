// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Compile binary signature predicates; prime arithmetic uses public projections
//! checked by the exact-mode adapter.
use crate::{
    compile::{
        algebra::gf2_128::Gf2_128Field,
        compiler::{compile_v2_shared_inputs, segment_circuit_v2},
        logic::{Logic, K_FIRST_WIRE_POSITION},
    },
    core::proto::v2::Circuit,
    mldsa::proto::{BinaryKeccak, MlDsaParams},
};
/// A binary circuit and the endpoint positions authenticated by a packed frontend.
pub struct CompiledPublic {
    pub circuit: Circuit<Gf2_128Field>,
    pub links: Vec<(Vec<usize>, Vec<usize>)>,
}
pub fn compile_circuit<P: MlDsaParams>(keccak: BinaryKeccak) -> Circuit<Gf2_128Field> {
    compile_public::<P>(keccak).circuit
}
pub fn compile_public<P: MlDsaParams>(keccak: BinaryKeccak) -> CompiledPublic {
    keccak.validate();
    let field = Gf2_128Field::new();
    let mut links = Vec::new();
    let (circuit, _, _) = compile_v2_shared_inputs(&field, |logic| {
        let mut pos = K_FIRST_WIRE_POSITION;
        let witness = circuits::allocate_private::<_, P>(&logic, &mut pos, keccak);
        links = witness.permutation_links(&logic);
        let mut external = Vec::new();
        for (a, b) in &links {
            for endpoint in [a, b] {
                external.push(endpoint[0] + 1..endpoint[endpoint.len() - 1] + 2);
            }
        }
        let checks = circuits::signature_assertions::<_, P>(&logic, witness, keccak);
        (
            logic.assert_all("mldsa_binary", &checks),
            K_FIRST_WIRE_POSITION,
            external,
        )
    });
    CompiledPublic {
        circuit: segment_circuit_v2(&field, circuit),
        links,
    }
}

mod hidden;
pub use hidden::compile_hidden;

pub(crate) mod circuits;

mod layout;
pub(crate) use layout::{key_bits, native_inputs, native_words};
