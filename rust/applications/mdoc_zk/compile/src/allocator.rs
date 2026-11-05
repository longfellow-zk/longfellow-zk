// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    circuits::{
        bit_plucker::BitPlucker,
        bitvec::{BitvecIO, V128},
    },
    compile::{
        algebra::field::CompileField,
        compiler::CompilerLogic,
        logic::{Eltw, LogicIO},
    },
};

pub struct WireAllocator<'l, 'a, FC: CompileField> {
    pub iologic: &'l CompilerLogic<'a, FC>,
    pub bitvec_io: &'l BitvecIO<'l, CompilerLogic<'a, FC>>,
    pub pos: usize,
}

impl<'l, 'a, FC: CompileField> WireAllocator<'l, 'a, FC> {
    pub fn new(
        iologic: &'l CompilerLogic<'a, FC>,
        bitvec_io: &'l BitvecIO<'l, CompilerLogic<'a, FC>>,
        pos: usize,
    ) -> Self {
        Self {
            iologic,
            bitvec_io,
            pos,
        }
    }

    pub fn allocate_wire(&mut self) -> Eltw<CompilerLogic<'a, FC>> {
        self.iologic.next(&mut self.pos)
    }

    pub fn allocate_bitvec<const N: usize>(
        &mut self,
    ) -> crate::circuits::bitvec::Bitvec<CompilerLogic<'a, FC>, N> {
        self.bitvec_io.next::<N>(&mut self.pos)
    }

    pub fn allocate_bitvec_array<const BITS: usize, const N: usize>(
        &mut self,
    ) -> [crate::circuits::bitvec::Bitvec<CompilerLogic<'a, FC>, BITS>; N] {
        std::array::from_fn(|_| self.allocate_bitvec())
    }
    pub fn allocate_binary_word(&mut self) -> Eltw<CompilerLogic<'a, FC>> {
        use crate::compile::logic::Logic;
        let bits = self.allocate_bitvec::<128>();
        let boolean = crate::circuits::boolean::Boolean::new(self.iologic);
        self.iologic.sum(
            &bits
                .as_array()
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    let mut bytes = vec![0; self.iologic.field().serialized_size_bytes()];
                    bytes[i / 8] = 1 << (i % 8);
                    let coefficient = self
                        .iologic
                        .field()
                        .bytes_to_element(&bytes)
                        .expect("binary polynomial basis coefficient");
                    self.iologic.mulk(&coefficient, &boolean.as_eltw(bit))
                })
                .collect::<Vec<_>>(),
        )
    }
    pub fn allocate_plucked_v128<const PLUCKER_WIDTH: usize>(
        &mut self,
        plucker: &BitPlucker<'_, CompilerLogic<'a, FC>, PLUCKER_WIDTH>,
    ) -> (
        V128<CompilerLogic<'a, FC>>,
        Vec<Eltw<CompilerLogic<'a, FC>>>,
    ) {
        let n_packed = 128 / PLUCKER_WIDTH;
        let packed: Vec<_> = (0..n_packed).map(|_| self.allocate_wire()).collect();
        let unpacked = plucker.unpack::<128>(&packed);
        (unpacked, packed)
    }

    pub fn allocate_tag_plucked<const PLUCKER_WIDTH: usize>(
        &mut self,
        plucker: &BitPlucker<'_, CompilerLogic<'a, FC>, PLUCKER_WIDTH>,
    ) -> (
        [V128<CompilerLogic<'a, FC>>; 2],
        [Vec<Eltw<CompilerLogic<'a, FC>>>; 2],
    ) {
        let (t0, p0) = self.allocate_plucked_v128::<PLUCKER_WIDTH>(plucker);
        let (t1, p1) = self.allocate_plucked_v128::<PLUCKER_WIDTH>(plucker);
        ([t0, t1], [p0, p1])
    }
}
