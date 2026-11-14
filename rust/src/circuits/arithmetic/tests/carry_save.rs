// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    circuits::{bitvec::BitvecLogic, boolean::Boolean},
    compile::{
        algebra::{field::CompileField, gf2_128::Gf2_128Field, p256::P256Field},
        logic::eval::EvalLogic,
    },
};

fn check<F: CompileField, const N: usize>(f: &F, values: impl IntoIterator<Item = [u64; 3]>) {
    let tracker = crate::compile::logic::tracker::AssertionTracker::new();
    let logic = EvalLogic::new_with_tracker(f, &tracker);
    let bits = BitvecLogic::new(&logic);
    let boolean = Boolean::new(&logic);
    for [a, b, c] in values {
        let (sum, carry, overflow) = bits.carry_save(
            &bits.of_u64::<N>(a),
            &bits.of_u64::<N>(b),
            &bits.of_u64::<N>(c),
        );
        let decode = |word: &crate::circuits::bitvec::Bitvec<_, N>| {
            word.iter().enumerate().fold(0u64, |value, (i, bit)| {
                value | (u64::from(boolean.as_eltw(bit).value == f.one()) << i)
            })
        };
        let high = u64::from(boolean.as_eltw(&overflow).value == f.one());
        assert_eq!(
            decode(&sum) + decode(&carry) + (high << N),
            a + b + c,
            "width={N}, addends={a},{b},{c}"
        );
    }
}

#[test]
fn carry_save_preserves_the_full_integer_sum_in_both_fields() {
    let exhaustive =
        || (0..8).flat_map(|a| (0..8).flat_map(move |b| (0..8).map(move |c| [a, b, c])));
    check::<_, 3>(&Gf2_128Field::new(), exhaustive());
    check::<_, 3>(&P256Field::new(), exhaustive());
    for values in [[0, 0, 0], [255, 255, 255], [128, 128, 128], [255, 1, 1]] {
        check::<_, 8>(&Gf2_128Field::new(), [values]);
        check::<_, 8>(&P256Field::new(), [values]);
    }
    check::<_, 17>(
        &Gf2_128Field::new(),
        [[65535, 1023, 10], [65535, 65535, 65535]],
    );
    check::<_, 17>(
        &P256Field::new(),
        [[65535, 1023, 10], [65535, 65535, 65535]],
    );
    check::<_, 0>(&Gf2_128Field::new(), [[0, 0, 0]]);
}
