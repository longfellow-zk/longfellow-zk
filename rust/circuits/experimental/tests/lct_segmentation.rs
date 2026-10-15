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

#[allow(dead_code)]
#[path = "../../../experiments/mldsa/morton.rs"]
mod morton;

fn run<F: core_algebra::AlgebraicField + core_algebra::SerializableField + Clone>(
    name: &str,
    f: &F,
    field_id: core_proto::FieldID,
) {
    let dir =
        std::env::var("LCT_CIRCUIT_DIR").unwrap_or_else(|_| "target/traversal-circuits".into());
    let bytes = std::fs::read(format!("{dir}/{name}--kind_abs_lex0213_r5.lfc2")).unwrap();
    let (circuit, rest) = core_proto::reader::CircuitReader::new(f, field_id)
        .from_bytes(&bytes, true)
        .unwrap();
    assert!(rest.is_empty());
    drop(bytes);
    morton::analyze_lct_segmentation(name, f, &circuit);
}

#[test]
#[ignore = "offline LCT1 segmentation sweep on saved current circuits"]
fn lct1_segmentation_sweep() {
    let name = std::env::var("LCT_DATASET").expect("set LCT_DATASET");
    match name.as_str() {
        "mdoc_hash2" => run(
            &name,
            &runtime_algebra::gf2_128::Gf2_128Field::new(),
            core_proto::FieldID::Gf2_128,
        ),
        "mdoc_sig" => run(
            &name,
            &runtime_algebra::p256::P256Field::new(),
            core_proto::FieldID::P256,
        ),
        "mldsa44" | "mldsa65" => run(
            &name,
            &circuits_experimental::mldsa::algebra::RuntimeFp24Ext6::new(),
            core_proto::FieldID::None,
        ),
        _ => panic!("unknown LCT_DATASET: {name}"),
    }
}
