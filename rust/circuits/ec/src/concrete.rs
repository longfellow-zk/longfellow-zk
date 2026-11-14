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

pub use crate::core::algebra::ec::*;

pub type Pt2<T> = (T, T);
pub type Pt3<T> = (T, T, T);

cfg_compiler! {
    use crate::{compile::{algebra::field::{CompileField, SupportsNatConversions}, logic::Logic}, core::algebra::ElementOf};

    pub fn evaluate_pt2<
        const W: usize,
        F: CompileField + SupportsNatConversions<W>,
        L: Logic<F = F>,
    >(
        pt: &Pt2<ElementOf<F>>,
        l: &L,
    ) -> Pt2<crate::compile::logic::Eltw<L>> {
        (l.konst(&pt.0), l.konst(&pt.1))
    }

    pub fn evaluate_pt3<
        const W: usize,
        F: CompileField + SupportsNatConversions<W>,
        L: Logic<F = F>,
    >(
        pt: &Pt3<ElementOf<F>>,
        l: &L,
    ) -> Pt3<crate::compile::logic::Eltw<L>> {
        (l.konst(&pt.0), l.konst(&pt.1), l.konst(&pt.2))
    }
}

cfg_testonly! {
    pub fn push_pt2<E: Clone>(value: &(E, E), dest: &mut Vec<E>) {
        dest.push(value.0.clone());
        dest.push(value.1.clone());
    }

    pub fn push_pt3<E: Clone>(value: &(E, E, E), dest: &mut Vec<E>) {
        dest.push(value.0.clone());
        dest.push(value.1.clone());
        dest.push(value.2.clone());
    }
}
