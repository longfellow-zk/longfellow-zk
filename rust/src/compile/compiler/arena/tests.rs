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

//! The constant arena keeps its values in place and drops all of them with
//! the arena, unlike the bump arena, which never runs destructors.

use std::rc::Rc;

use super::DropArena;

#[test]
fn constants_are_dropped_with_the_arena() {
    let owner = Rc::new(());
    // Several chunks: 64 + 128 + 256 + 512 slots, and part of the next.
    let count = 1500;
    {
        let arena = DropArena::new();
        let held: Vec<_> = (0..count)
            .map(|i| arena.alloc((i, owner.clone())))
            .collect();
        assert_eq!(Rc::strong_count(&owner), count + 1);
        // Every reference handed out stays valid and in place while more
        // values are allocated.
        for (i, value) in held.iter().enumerate() {
            assert_eq!(value.0, i);
        }
    }
    assert_eq!(Rc::strong_count(&owner), 1, "the arena leaked values");
}

#[test]
fn an_empty_arena_and_exact_chunk_boundaries_drop_cleanly() {
    let owner = Rc::new(());
    drop(DropArena::<Rc<()>>::new());
    for count in [1, 64, 65, 192, 193] {
        let arena = DropArena::new();
        for _ in 0..count {
            arena.alloc(owner.clone());
        }
        assert_eq!(Rc::strong_count(&owner), count + 1);
        drop(arena);
        assert_eq!(Rc::strong_count(&owner), 1);
    }
}
