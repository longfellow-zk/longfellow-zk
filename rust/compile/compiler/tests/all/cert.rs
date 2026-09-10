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

//! Tests for the proof certificate sidecar (Phase R0 of
//! `formal/circuits/CIRCUIT_PROOF_PLAN.md`).

use compile_algebra::p256::P256Field;
use compile_compiler::cert::{build_sidecar, parse_sidecar, InputLayoutEntry, CERT_MAGIC};
use compile_compiler::compile_with_cert;
use compile_logic::{Logic, LogicIO};
use core_proto::FieldID;

const LAYOUT: &[InputLayoutEntry<'static>] = &[
    InputLayoutEntry {
        position: 0,
        name: "one",
    },
    InputLayoutEntry {
        position: 1,
        name: "w1",
    },
    InputLayoutEntry {
        position: 2,
        name: "w2",
    },
];

fn compile_micro() -> (
    core_proto::circuit::Circuit<P256Field>,
    compile_compiler::debug::CircuitDebugSymbols,
    compile_compiler::ScheduleInfo<P256Field>,
) {
    let f = P256Field::new();
    let (circuit, _info, symbols, schedule_info) = compile_with_cert(&f, |l| {
        let w1 = l.input(1);
        let w2 = l.input(2);

        let q1 = l.mul(&w1, &w1);
        let q2 = l.mul(&w2, &w2);

        let assert1 = l.assert0("check_w1", &q1);
        let assert2 = l.assert0("check_w2", &q2);

        let block_a = l.assert_all("block_a", &[assert1]);
        let block_b = l.assert_all("block_b", &[assert2]);
        let root = l.assert_all("root", &[block_a, block_b]);
        (root, 1, 0)
    });
    (circuit, symbols, schedule_info)
}

#[test]
fn test_sidecar_roundtrip_and_id() {
    let f = P256Field::new();
    let (circuit, symbols, schedule_info) = compile_micro();

    let bytes = build_sidecar(
        &f,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        LAYOUT,
    );
    let parsed = parse_sidecar(&bytes).expect("sidecar must parse");

    assert_eq!(parsed.version, 2);
    assert_eq!(parsed.field_id, FieldID::P256 as u32);
    assert_eq!(parsed.id, circuit.id);
    assert_eq!(parsed.ninput, 3);

    // Every assertion instantiates a template, and its mapping covers that template's nodes.
    assert!(!parsed.templates.is_empty());
    for a in &parsed.assertions {
        assert!(a.template < parsed.templates.len());
        assert_eq!(a.mapping.len(), parsed.templates[a.template].nodes.len());
    }
    assert_eq!(parsed.npublic_input, 1);

    // The sidecar's expanded terms fully determine the shipped circuit: the
    // recomputed canonical id matches the production artifact's id.
    let rf = runtime_algebra::p256::P256Field::new();
    let recomputed = parsed.recompute_id(&rf).expect("recompute_id");
    assert_eq!(recomputed, circuit.id);

    // Assertion paths survive compilation and land on distinct wires.
    let paths: Vec<&String> = parsed
        .assertions
        .iter()
        .flat_map(|a| a.paths.iter())
        .collect();
    assert!(paths.contains(&&"root/block_a/check_w1".to_string()));
    assert!(paths.contains(&&"root/block_b/check_w2".to_string()));
    assert_eq!(parsed.assertions.len(), 2);

    // Input layout round-trips.
    assert_eq!(parsed.input_layout.len(), 3);
    assert_eq!(parsed.input_layout[1], (1, "w1".to_string()));

    // Every sum node has a wire inside the circuit layers, and every input
    // node sits at the input pseudo-layer.
    for (i, node) in parsed.nodes.iter().enumerate() {
        match node {
            compile_compiler::cert::ParsedNode::Input { .. } => {
                let (layer, _) = parsed.node_wires[i].expect("input node must have a wire");
                assert_eq!(layer, parsed.layers.len());
            }
            compile_compiler::cert::ParsedNode::Sum { .. } => {
                let (layer, _) = parsed.node_wires[i].expect("sum node must have a wire");
                assert!(layer < parsed.layers.len());
            }
            compile_compiler::cert::ParsedNode::Assert0 { .. } => {
                assert!(parsed.node_wires[i].is_none());
            }
        }
    }
}

#[test]
fn test_sidecar_assertion_layer_attribution() {
    let f = P256Field::new();
    let (circuit, _info, symbols, schedule_info) = compile_with_cert(&f, |l| {
        let x = l.input(1);
        let square = l.mul(&x, &x);
        let fourth_power = l.mul(&square, &square);

        let input_assertion = l.assert0("input", &x);
        let output_assertion = l.assert0("output", &fourth_power);
        let root = l.assert_all("root", &[input_assertion, output_assertion]);
        (root, 1, 0)
    });

    let layout = [
        InputLayoutEntry {
            position: 0,
            name: "one",
        },
        InputLayoutEntry {
            position: 1,
            name: "x",
        },
    ];
    let bytes = build_sidecar(
        &f,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        &layout,
    );
    let parsed = parse_sidecar(&bytes).expect("sidecar must parse");

    let input_rec = parsed
        .assertions
        .iter()
        .find(|a| a.paths.iter().any(|p| p == "root/input"))
        .expect("root/input assertion");
    let output_rec = parsed
        .assertions
        .iter()
        .find(|a| a.paths.iter().any(|p| p == "root/output"))
        .expect("root/output assertion");

    // Matches the debug-symbol layer attribution: the mid-circuit assertion
    // is materialized one layer above the input layer, the last-layer
    // assertion lands on the output wires.
    assert_eq!(input_rec.wire_layer, 1);
    assert_eq!(output_rec.wire_layer, 0);
}

#[test]
fn test_sidecar_merged_assertions_carry_all_paths() {
    let f = P256Field::new();
    let (circuit, _info, symbols, schedule_info) = compile_with_cert(&f, |l| {
        let x = l.input(1);
        let q = l.mul(&x, &x);

        // Structurally identical assertions under different names: the
        // compiler merges them, and the sidecar must list both paths.
        let a1 = l.assert0("same_a", &q);
        let a2 = l.assert0("same_b", &q);
        let root = l.assert_all("root", &[a1, a2]);
        (root, 1, 0)
    });

    let layout = [
        InputLayoutEntry {
            position: 0,
            name: "one",
        },
        InputLayoutEntry {
            position: 1,
            name: "x",
        },
    ];
    let bytes = build_sidecar(
        &f,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        &layout,
    );
    let parsed = parse_sidecar(&bytes).expect("sidecar must parse");

    assert_eq!(
        parsed.assertions.len(),
        1,
        "merged assertions share one wire"
    );
    let paths = &parsed.assertions[0].paths;
    assert!(paths.contains(&"root/same_a".to_string()));
    assert!(paths.contains(&"root/same_b".to_string()));
}

#[test]
fn test_sidecar_deterministic() {
    let f = P256Field::new();

    let (circuit1, symbols1, info1) = compile_micro();
    let (circuit2, symbols2, info2) = compile_micro();
    assert_eq!(circuit1.id, circuit2.id);

    let bytes1 = build_sidecar(&f, FieldID::P256, &circuit1, &symbols1, &info1, LAYOUT);
    let bytes2 = build_sidecar(&f, FieldID::P256, &circuit2, &symbols2, &info2, LAYOUT);
    assert_eq!(
        bytes1, bytes2,
        "sidecar must be byte-for-byte deterministic"
    );

    assert_eq!(&bytes1[..8], &CERT_MAGIC);
    assert_eq!(&bytes1[bytes1.len() - 8..], &CERT_MAGIC);
}

#[test]
fn test_sidecar_parser_rejects_garbage() {
    let f = P256Field::new();
    let (circuit, symbols, schedule_info) = compile_micro();
    let mut bytes = build_sidecar(
        &f,
        FieldID::P256,
        &circuit,
        &symbols,
        &schedule_info,
        LAYOUT,
    );

    // Bad magic.
    let mut bad_head = bytes.clone();
    bad_head[0] ^= 0xFF;
    assert!(parse_sidecar(&bad_head).is_err());

    // Bad trailing magic.
    let mut bad_tail = bytes.clone();
    let last = bad_tail.len() - 1;
    bad_tail[last] ^= 0xFF;
    assert!(parse_sidecar(&bad_tail).is_err());

    // Truncation.
    bytes.truncate(bytes.len() / 2);
    assert!(parse_sidecar(&bytes).is_err());
}
