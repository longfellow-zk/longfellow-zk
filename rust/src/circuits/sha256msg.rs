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

mod concrete;
mod shape;

pub use concrete::{
    derived, given, given_and_derived, pad_sha256_message, sha256_msg_derived, ConcreteGiven,
};
pub use shape::Derived;

cfg_compiler! {
    mod allocate;
    mod circuit;

    pub use self::{
        allocate::allocate_given,
        circuit::{pack_digest, Given, Sha256Msg},
    };
}

cfg_testonly! {
    mod evaluate;
    pub use evaluate::evaluate_given;
}

#[cfg(test)]
mod tests;
