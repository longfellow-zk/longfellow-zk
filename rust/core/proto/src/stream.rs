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

//! Dictionary-compressed runs shared by circuit compression backends.

#[derive(Clone, Debug)]
pub struct Stream<T> {
    pub deltas: Vec<T>,
    pub segments: Vec<Vec<u32>>,
    pub tokens: Vec<u32>,
}
impl<T> Default for Stream<T> {
    fn default() -> Self {
        Self {
            deltas: Vec::new(),
            segments: Vec::new(),
            tokens: Vec::new(),
        }
    }
}
impl<T> Stream<T> {
    pub fn num_terms(&self) -> usize {
        self.tokens
            .iter()
            .map(|&t| self.segments[t as usize].len())
            .sum()
    }
}
