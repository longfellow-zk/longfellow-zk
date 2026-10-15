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

//! Offline preparation benchmarks. No policy selection is used by the prover.

#[path = "../../../experiments/mldsa/hquad_sort.rs"]
mod candidates;
#[path = "support/memory.rs"]
mod memory;

use core_algebra::SerializableField;
use core_proto::{circuit::Circuit, reader::CircuitReader, FieldID};
use runtime_algebra::{RuntimeField, SupportsSampling};
use runtime_random::{RandomEngine, Transcript};
use std::{hint::black_box, time::Instant};

fn sweep<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling<W>>(
    dataset: &str,
    f: &F,
    id: FieldID,
) {
    let dir =
        std::env::var("HQUAD_CIRCUIT_DIR").unwrap_or_else(|_| "target/traversal-circuits".into());
    let bytes = std::fs::read(format!("{dir}/{dataset}--kind_abs_lex0213_r5.lfc2")).unwrap();
    let (circuit, rest): (Circuit<F>, _) =
        CircuitReader::new(f, id).from_bytes(&bytes, true).unwrap();
    assert!(rest.is_empty());
    let repeats: usize = std::env::var("HQUAD_REPEATS")
        .unwrap_or_else(|_| "3".into())
        .parse()
        .unwrap();
    let only = std::env::var("HQUAD_CANDIDATE").ok();
    assert!(repeats > 0);
    assert!(only
        .as_ref()
        .is_none_or(|name| candidates::NAMES.contains(&name.as_str())));
    let mut totals = vec![vec![0.0; repeats]; candidates::NAMES.len()];
    let mut peaks = vec![0; candidates::NAMES.len()];
    let mut sizes = vec![0; candidates::NAMES.len()];
    let mut rng = Transcript::new(b"hquad-preparation-sweep");
    let beta = rng.elt_field(f);
    let mut nv = circuit.raw.noutput;
    let mut logv = circuit.raw.logv;
    for (ly, layer) in circuit.raw.layers.iter().enumerate() {
        let r0 = rng.elt_field_slice(logv, f);
        let r1 = rng.elt_field_slice(logv, f);
        let alpha = rng.elt_field(f);
        let g = if nv == 0 {
            Vec::new()
        } else {
            runtime_sumcheck::eq::eq2(logv, nv, &r0, &r1, &alpha, f)
        };
        // Keep the historical sorting reference local to this offline experiment.
        // The production round-major prover now requires preordered circuits.
        let expected =
            candidates::prepare("index-cycle", layer, &circuit.raw.constants, &g, &beta, f);
        // Repeat is the second index of the candidate-by-repeat table.
        #[allow(clippy::needless_range_loop)]
        for repeat in 0..repeats {
            // Rotate evaluation order to avoid always favoring one candidate.
            for shift in 0..candidates::NAMES.len() {
                let i = (shift + repeat + ly) % candidates::NAMES.len();
                let name = candidates::NAMES[i];
                if only.as_ref().is_some_and(|n| n != name) {
                    continue;
                }
                let memory = memory::Measurement::start();
                let start = Instant::now();
                let got = candidates::prepare(name, layer, &circuit.raw.constants, &g, &beta, f);
                totals[i][repeat] += start.elapsed().as_secs_f64() * 1000.;
                peaks[i] = peaks[i].max(memory.finish().additional());
                sizes[i] = sizes[i].max(
                    got.hc.capacity() * std::mem::size_of::<runtime_sumcheck::hquad::HCorner>()
                        + got.vc.capacity() * std::mem::size_of::<F::E>(),
                );
                assert_eq!(got.hc.len(), expected.hc.len(), "{name} layer {ly}");
                for (a, b) in got.hc.iter().zip(&expected.hc) {
                    assert_eq!(a.h, b.h, "{name} layer {ly}");
                }
                assert_eq!(got.vc, expected.vc, "{name} layer {ly}");
                black_box(got);
            }
        }
        nv = layer.nw();
        logv = layer.logw();
    }
    for (i, candidate) in candidates::NAMES.iter().enumerate() {
        if only.as_ref().is_some_and(|n| n != candidate) {
            continue;
        }
        println!(
            "PREP dataset={dataset} candidate={candidate} ms={:?} peak={} retained_max={}",
            totals[i], peaks[i], sizes[i]
        );
    }
}

#[test]
#[ignore = "offline HQuad preparation sweep"]
fn hquad_preparation_sweep() {
    use circuits_experimental::mldsa::algebra::RuntimeFp24Ext6;
    use runtime_algebra::{gf2_128::Gf2_128Field, p256::P256Field};
    let dataset = std::env::var("HQUAD_DATASET").unwrap_or_else(|_| "all".into());
    assert!(["all", "mdoc_hash2", "mdoc_sig", "mldsa44", "mldsa65"].contains(&dataset.as_str()));
    let gf = Gf2_128Field::new();
    let fp = P256Field::new();
    let ext = RuntimeFp24Ext6::new();
    if dataset == "all" || dataset == "mdoc_hash2" {
        sweep("mdoc_hash2", &gf, FieldID::Gf2_128);
    }
    if dataset == "all" || dataset == "mdoc_sig" {
        sweep("mdoc_sig", &fp, FieldID::P256);
    }
    if dataset == "all" || dataset == "mldsa44" {
        sweep("mldsa44", &ext, FieldID::None);
    }
    if dataset == "all" || dataset == "mldsa65" {
        sweep("mldsa65", &ext, FieldID::None);
    }
}
