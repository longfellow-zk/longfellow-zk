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

use crate::core::bits::{
    recipe::{BitOp, BitRecipe},
    PackedBits,
};
#[test]
fn boolean_recipe_round_trip_and_malformed_inputs() {
    let recipe = BitRecipe {
        nodes: vec![
            BitOp::Input(0),
            BitOp::Input(1),
            BitOp::Xor(0, 1),
            BitOp::And(0, 2),
            BitOp::Constant(true),
        ],
        outputs: vec![2, 3, 4],
    };
    let bits = [true, false].into_iter().collect::<PackedBits>();
    let result = recipe.evaluate(&bits).unwrap();
    assert_eq!(result, [true, true, true].into_iter().collect());
    let bytes = recipe.to_bytes();
    assert_eq!(BitRecipe::from_bytes(&bytes).unwrap(), recipe);
    for n in 0..bytes.len() {
        assert!(BitRecipe::from_bytes(&bytes[..n]).is_err())
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(BitRecipe::from_bytes(&trailing).is_err());
    assert!(recipe.evaluate(&PackedBits::default()).is_err());
    assert!(BitRecipe {
        nodes: vec![BitOp::Xor(0, 0)],
        outputs: vec![0]
    }
    .validate(2)
    .is_err());
    assert_eq!(bits.word128(usize::MAX), 0);
}
