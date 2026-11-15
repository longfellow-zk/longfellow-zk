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

use crate::compile::logic::{Eltw, Logic};

pub struct Polynomial<'a, L: Logic> {
    logic: &'a L,
}

impl<'a, L: Logic> Polynomial<'a, L> {
    pub fn new(logic: &'a L) -> Self {
        Self { logic }
    }

    fn powers_of_x(&self, n: usize, x: &Eltw<L>) -> Vec<Eltw<L>> {
        let mut xi = vec![self.logic.zero(); n];
        if n > 0 {
            xi[0] = self.logic.one();
            if n > 1 {
                xi[1] = x.clone();
                for k in 2..n {
                    xi[k] = self.logic.mul(&xi[k / 2], &xi[k - (k / 2)]);
                }
            }
        }
        xi
    }

    pub fn eval(&self, cc: &[Eltw<L>], x: &Eltw<L>) -> Eltw<L> {
        let n = cc.len();
        let xi = self.powers_of_x(n, x);
        self.logic.dot(cc, &xi)
    }

    // parallel Horner rule
}
