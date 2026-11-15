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

mod points;
pub use points::{Pt2, Pt3};

cfg_compiler! {
    mod circuit;
    pub use circuit::{pt2_wires, EcCircuit};
}

cfg_testonly! {
    mod evaluate;
    pub use evaluate::{evaluate_pt2, evaluate_pt3, push_pt2};
}

#[cfg(test)]
mod tests;
