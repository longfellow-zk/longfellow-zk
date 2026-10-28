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

//! Protocol kernel timings; public preprocessing reported separately.
use std::time::Instant;

use longfellow_zk::{
    core::algebra::SerializableField,
    runtime::{
        algebra::{EvaluationDomain, RuntimeField, SupportsSampling},
        polygero::*,
        proto::Digest,
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};
fn run<
    const W: usize,
    F: RuntimeField<W> + SerializableField + SupportsSampling,
    D: EvaluationDomain<W, F>,
>(
    name: &str,
    f: &F,
    d: &D,
    config: PolygeroConfig,
    nw: usize,
) {
    let mut rng = DeterministicRng::new(42);
    let mut witness = rng.elt_field_slice(nw, f);
    let products: Vec<_> = (0..nw / 3)
        .map(|i| {
            let x = 3 * i;
            witness[x + 2] = f.mulf(&witness[x], &witness[x + 1]);
            PolygeroProductConstraint {
                x,
                y: x + 1,
                z: x + 2,
            }
        })
        .collect();
    let mut b = vec![f.zero(); 8];
    let a: Vec<_> = witness
        .iter()
        .enumerate()
        .map(|(w, value)| {
            let k = rng.elt_field(f);
            let c = w % 8;
            f.sub(&mut b[c], &f.mulf(&k, value));
            PolygeroLinearTerm { c, w, k }
        })
        .collect();
    // The public fixture recipe (backend, size, seed and generator version)
    // determines the benchmark statement independently of sparse term storage.
    let mut fixture = Transcript::new(b"polygero/kernel/fixture/v1");
    fixture.write_bytes(name.as_bytes());
    fixture.write_bytes(&(nw as u64).to_le_bytes());
    fixture.write_bytes(&42u64.to_le_bytes());
    let statement = Digest {
        data: fixture.bytes(32).try_into().unwrap(),
    };
    let preprocessing_start = Instant::now();
    let param = PolygeroParam::try_new(nw, &products, config, d, f).unwrap();
    let vp = PolygeroParam::try_new(nw, &products, config, d, f).unwrap();
    let preprocessing = preprocessing_start.elapsed();
    // Release the prover's rows and Merkle tree before timing verification.
    let (com, bytes, commit, prove) = {
        let mut ts = Transcript::new(b"polygero/kernel/bench");
        let commit_start = Instant::now();
        let (prover, com) =
            PolygeroProver::commit(witness, param, &mut ts, d, &mut rng, f).unwrap();
        let commit = commit_start.elapsed();
        let prove_start = Instant::now();
        let proof = prover.prove(&b, &mut ts, &a, &statement, d, f).unwrap();
        let prove = prove_start.elapsed();
        let bytes = proof.write(&vp.geometry(), f).unwrap();
        (com, bytes, commit, prove)
    };
    let verify_start = Instant::now();
    let decoded_proof =
        longfellow_zk::runtime::proto::polygero::read(&mut bytes.as_slice(), &vp.geometry(), f)
            .unwrap();
    let mut verifier_ts = Transcript::new(b"polygero/kernel/bench");
    let mut verifier = PolygeroVerifier::new(vp);
    verifier.receive_commitment(&com, &mut verifier_ts);
    verifier
        .verify(
            &b,
            &com,
            &decoded_proof,
            &a,
            &statement,
            &mut verifier_ts,
            d,
            f,
        )
        .unwrap();
    let verify = verify_start.elapsed();
    eprintln!("{name}: config={config:?}, witnesses={nw}, preprocessing(two parties)={:.3} ms, commit={:.3} ms, prove={:.3} ms, decode+verify={:.3} ms, proof={} bytes",preprocessing.as_secs_f64()*1000.0,commit.as_secs_f64()*1000.0,prove.as_secs_f64()*1000.0,verify.as_secs_f64()*1000.0,bytes.len());
}
const BENCH_CONFIG: PolygeroConfig = PolygeroConfig {
    k: 512,
    s: 64,
    n: 8192,
    t: 64,
};

fn main() {
    use longfellow_zk::runtime::algebra::{
        fp2::Fp2Field,
        gf2_128::Gf2_128Field,
        p256::P256Field,
        q256::Q256Field,
        range_interpolation::{
            BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
            ScalarInterpolatorFactory,
        },
        subfield_v1::BinarySubfield,
        SupportsFFT,
    };
    eprintln!("UNCERTIFIED PROTOTYPE PARAMETERS; kernel timings exclude witness generation and public preprocessing.");
    {
        let f = Gf2_128Field::new();
        let sf = BinarySubfield::new(&longfellow_zk::core::algebra::proto::GF2_16_BASIS_V1);
        let d = BinaryInterpolatorFactory::new(&f, &sf);
        run("binary", &f, &d, BENCH_CONFIG, 8192);
    }
    {
        let f = P256Field::new();
        let f2 = Fp2Field::new(&f);
        let d =
            QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
        run("p256", &f, &d, BENCH_CONFIG, 8192);
    }
    {
        let f = Q256Field::new();
        let d = ScalarInterpolatorFactory::new(&f, 128);
        run(
            "q256 scalar reference (small workload)",
            &f,
            &d,
            PolygeroConfig {
                k: 8,
                s: 2,
                n: 64,
                t: 2,
            },
            30,
        );
    }
    #[cfg(feature = "experimental")]
    {
        use longfellow_zk::runtime::algebra::{
            fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
        };
        let f = RuntimeFp24Ext6::new();
        run("extension", &f, &CrtInterpolatorFactory, BENCH_CONFIG, 8192);
    }
}
