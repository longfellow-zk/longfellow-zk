// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
#[test]
fn reconstructed_mac_inputs_are_checked_by_the_circuit() {
    use crate::{
        core::{
            algebra::AlgebraicField,
            proto::{reader::CircuitReader, writer::CircuitWriter, FieldID},
        },
        runtime::{
            algebra::gf2_128::{Gf2_128, Gf2_128Field},
            sumcheck_v2,
        },
    };
    let fc = crate::compile::algebra::gf2_128::Gf2_128Field::new();
    let mut public_count = 0;
    let (compiled, _, _) = crate::compile::compiler::compile_v2(&fc, |logic| {
        let bv = crate::circuits::bitvec::BitvecLogic::new(&logic);
        let io = BitvecIO::new(&bv);
        let mut allocator =
            WireAllocator::new_boolean(&logic, &io, crate::compile::logic::K_FIRST_WIRE_POSITION);
        let av = allocator.allocate_field_input();
        let tags = [
            allocator.allocate_field_input(),
            allocator.allocate_field_input(),
        ];
        public_count = allocator.pos;
        let message = allocator.allocate_bitvec::<256>();
        let pads = [
            allocator.allocate_field_input(),
            allocator.allocate_field_input(),
        ];
        let given = crate::circuits::mac_gf128::Given {
            message,
            mac_av: av,
            mac_ap: pads,
            tag: tags,
        };
        (
            crate::circuits::mac_gf128::MAC::new(&logic).assert_mac(&given),
            public_count,
            0,
        )
    });
    let bytes = CircuitWriter::new(&fc, FieldID::Gf2_128).to_bytes_lfc2(&compiled);
    let f = Gf2_128Field::new();
    let (circuit, tail) = CircuitReader::new(&f, FieldID::Gf2_128)
        .from_bytes_lfc2(&bytes, false)
        .unwrap();
    assert!(tail.is_empty());
    let message = std::array::from_fn::<_, 32, _>(|i| (i * 13 + 7) as u8);
    let av = 0x123456789abcdefu128;
    let pads = [0xabcdef123456789u128, 0xdeadbeef1234u128];
    let tags = crate::circuits::mac::concrete::compute_tag(&message, av, &pads);
    let mut inputs = vec![f.one()];
    let mut word = |value: u128| {
        inputs.extend((0..128).map(|i| Gf2_128::from((value >> i) & 1)));
    };
    word(av);
    word(tags[0]);
    word(tags[1]);
    assert_eq!(inputs.len(), public_count);
    inputs.extend(
        message
            .iter()
            .flat_map(|b| (0..8).map(move |i| Gf2_128::from(u128::from((b >> i) & 1)))),
    );
    for value in pads {
        inputs.extend((0..128).map(|i| Gf2_128::from((value >> i) & 1)));
    }
    assert_eq!(inputs.len(), circuit.raw.ninput);
    sumcheck_v2::eval_circuit(inputs.clone(), &circuit, &f).unwrap();
    // Reject changed public tags/challenge, changed message bits, and either private mask.
    for index in [
        1,
        129,
        257,
        public_count,
        public_count + 256,
        public_count + 384,
    ] {
        let mut invalid = inputs.clone();
        f.add(&mut invalid[index], &f.one());
        assert!(
            sumcheck_v2::eval_circuit(invalid, &circuit, &f).is_err(),
            "input {index}"
        );
    }
}
