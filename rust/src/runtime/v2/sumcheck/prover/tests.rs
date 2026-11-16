// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0

pub(super) mod fixtures;

/// Sumcheck pads are their own owned type, used once (sumcheck I6, audit
/// S1): not `Clone`, so one sample cannot mask two runs, and laid out as the
/// committed copy `sample_pads` returns with them.
#[test]
fn pads_are_owned_one_use_values_matching_their_committed_copy() {
    use super::{sample_pads, SumcheckPads};
    use crate::runtime::{
        algebra::gf2_128::Gf2_128Field, random::DeterministicRng,
        v2::proto::sumcheck::SumcheckProofGeometry,
    };
    // Resolves only if exactly one impl applies, that is, if `T` is not Clone.
    trait AmbiguousIfClone<A> {
        fn check() {}
    }
    impl<T> AmbiguousIfClone<()> for T {}
    struct IsClone;
    impl<T: Clone> AmbiguousIfClone<IsClone> for T {}
    <SumcheckPads<Gf2_128Field> as AmbiguousIfClone<_>>::check();

    let f = Gf2_128Field::new();
    let geometry = SumcheckProofGeometry::new(vec![2, 0]).unwrap();
    let (pads, cells) = sample_pads::<_, _>(&geometry, &mut DeterministicRng::new(3), &f);
    pads.validate(&geometry).unwrap();
    assert!(pads
        .validate(&SumcheckProofGeometry::new(vec![1, 0]).unwrap())
        .is_err());
    assert_eq!(cells.len(), geometry.pad_count());
    let layout = geometry.pad_layout(0);
    for (layer, at) in pads.as_proof().layers.iter().zip(&layout.layers) {
        for (round, slots) in layer.rounds.iter().zip(&at.rounds) {
            assert_eq!(round.coefficients, slots.map(|i| cells[i]));
        }
        assert_eq!(layer.claims, at.claims.map(|i| cells[i]));
        assert_eq!(layer.cross, cells[at.cross]);
    }
}
