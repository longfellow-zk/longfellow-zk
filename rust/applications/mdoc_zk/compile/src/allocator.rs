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
    circuits::bitvec::BitvecIO,
    compile::{algebra::field::CompileField, compiler::CompilerLogic},
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
}
