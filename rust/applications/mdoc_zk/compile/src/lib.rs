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

pub mod allocate_hash;
pub mod allocate_sig;
pub mod allocator;
pub mod generate_hash;
pub mod generate_sig;

pub use allocate_hash::*;
pub use allocate_sig::*;
pub use allocator::*;
pub use generate_hash::*;
pub use generate_sig::*;

use crate::compile::algebra::{gf2_128::Gf2_128Field, p256::P256Field};

/// Generate NEXT v9 circuits independently of runtime parameter selection.
pub fn compile_circuits(num_attrs: usize) -> Result<Vec<u8>, String> {
    let f = Gf2_128Field::new();
    let p = P256Field::new();
    let sig = generate_sig_v2_circuit(&p)?;
    let (hash, manifest) = generate_hash_v2_circuit(&f, num_attrs)?;
    let mut b = crate::core::proto::archive::CircuitArchiveBuilder::new();
    b.set_circuit_version(crate::mdoc::circuits::NEXT_VERSION as u32);
    b.add_entry(
        "sig",
        sig.id,
        crate::core::proto::writer::CircuitWriter::new(&p, crate::core::proto::FieldID::P256)
            .to_bytes_lfc3(&sig),
    );
    b.add_entry(
        "hash",
        hash.id,
        crate::core::proto::writer::CircuitWriter::new(&f, crate::core::proto::FieldID::Gf2_128)
            .to_bytes_lfc3(&hash),
    );
    b.add_entry("hash-input", manifest.digest(), manifest.to_bytes());
    Ok(b.build().to_bytes())
}
pub use compile_circuits as generate_circuits;

pub fn compile_all_circuits() -> Vec<Result<Vec<u8>, String>> {
    std::thread::scope(|scope| {
        let tasks: Vec<_> = (1..=4)
            .map(|n| scope.spawn(move || compile_circuits(n)))
            .collect();
        tasks
            .into_iter()
            .map(|task| task.join().expect("circuit compiler panicked"))
            .collect()
    })
}
pub use compile_all_circuits as generate_all_circuits;
