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

//! V1 absolute quadratic terms and canonical operand ordering.

use std::fmt;

use crate::core::algebra::SerializableField;

pub struct Term<F: SerializableField> {
    pub k: F::E,
    pub g: u32,
    pub h0: u32,
    pub h1: u32,
}

impl<F: SerializableField> Clone for Term<F> {
    fn clone(&self) -> Self {
        Term {
            k: self.k.clone(),
            g: self.g,
            h0: self.h0,
            h1: self.h1,
        }
    }
}

impl<F: SerializableField> PartialEq for Term<F>
where F::E: PartialEq
{
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g && self.h0 == other.h0 && self.h1 == other.h1 && self.k == other.k
    }
}

impl<F: SerializableField> Eq for Term<F> where F::E: Eq {}

impl<F: SerializableField> fmt::Debug for Term<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Term")
            .field("k", &self.k)
            .field("g", &self.g)
            .field("h0", &self.h0)
            .field("h1", &self.h1)
            .finish()
    }
}

pub fn canonical_term<F: SerializableField>(t: Term<F>) -> Term<F> {
    if t.h1 < t.h0 {
        Term {
            k: t.k,
            g: t.g,
            h0: t.h1,
            h1: t.h0,
        }
    } else {
        t
    }
}
