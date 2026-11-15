// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use crate::{
    circuits::boolean::{Bitw, BooleanIO},
    compile::logic::LogicIO,
    mldsa::proto::{MlDsaParams, N},
};
type BitDecompositions<L> = Vec<Vec<Vec<Bitw<L>>>>;

pub(crate) struct Shared<L: LogicIO> {
    pub z: BitDecompositions<L>,
    pub h: BitDecompositions<L>,
    pub raw: BitDecompositions<L>,
    pub auxiliary: BitDecompositions<L>,
    pub hinted: BitDecompositions<L>,
    pub positive: Vec<Bitw<L>>,
    pub negative: Vec<Bitw<L>>,
}

impl<L: LogicIO> Shared<L> {
    pub(crate) fn input<P: MlDsaParams>(logic: &L, pos: &mut usize) -> Self {
        let io = BooleanIO::new(logic);
        let next = |position: &mut usize| io.next(position);
        let mut read = |polynomials, width| {
            (0..polynomials)
                .map(|_| {
                    (0..N)
                        .map(|_| (0..width).map(|_| next(pos)).collect())
                        .collect()
                })
                .collect()
        };
        let z = read(P::L, P::Z_BITS);
        let h = read(P::K, 1);
        let raw = read(P::K, P::R1_BITS);
        let auxiliary = read(P::K, P::r0_bits() + 1);
        let hinted = read(P::K, P::R1_BITS);
        let positive = (0..N).map(|_| next(pos)).collect();
        let negative = (0..N).map(|_| next(pos)).collect();
        Self {
            z,
            h,
            raw,
            auxiliary,
            hinted,
            positive,
            negative,
        }
    }
}
