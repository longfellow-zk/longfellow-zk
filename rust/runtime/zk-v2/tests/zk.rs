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

use super::{ZkContext, ZkProof, ZkProver, ZkVerifier};
use crate::{
    core::{
        algebra::SerializableField,
        proto::{
            circuit::{compute_id, Circuit, RawCircuit},
            Layer, TermDelta,
        },
    },
    runtime::{
        algebra::{
            EvaluationDomain, RangeInterpolatorFactory, RuntimeField, SubfieldV1, SupportsSampling,
            ZkField,
        },
        polygero::PolygeroConfig,
        random::{DeterministicRng, Transcript},
    },
};

struct FullField<'a, const W: usize, F>(&'a F);
impl<const W: usize, F: RuntimeField<W> + SerializableField + SupportsSampling> SubfieldV1
    for FullField<'_, W, F>
{
    type E = F::E;
    fn to_bytes_into(&self, e: &F::E, dst: &mut [u8]) {
        self.0.to_bytes_into(e, dst);
    }
    fn contains(&self, _: &F::E) -> bool {
        true
    }
    fn serialized_size_bytes(&self) -> usize {
        self.0.serialized_size_bytes()
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<F::E, String> {
        self.0.bytes_to_element(b)
    }
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, r: R) -> F::E {
        self.0.sample(r)
    }
}
// This wrapper exposes only the range API and enforces the original point-table bound.
// Every core and V2 proof must work with only the original k+n point table.
struct BoundedDomain<'a, D> {
    inner: &'a D,
    limit: usize,
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> RangeInterpolatorFactory<W, F>
    for BoundedDomain<'_, D>
{
    type Plan = D::Plan;
    fn can_interpolate(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> bool {
        source.end <= self.limit
            && destination.end <= self.limit
            && self.inner.can_interpolate(source, destination)
    }
    fn make_range(
        &self,
        source: std::ops::Range<usize>,
        destination: std::ops::Range<usize>,
    ) -> Self::Plan {
        assert!(
            self.can_interpolate(source.clone(), destination.clone()),
            "new domain points requested"
        );
        self.inner.make_range(source, destination)
    }
    fn point(&self, index: usize) -> F::E {
        assert!(index < self.limit, "new domain point requested");
        self.inner.point(index)
    }
}
impl<const W: usize, F: RuntimeField<W>, D: EvaluationDomain<W, F>> EvaluationDomain<W, F>
    for BoundedDomain<'_, D>
{
    fn domain_id(&self) -> Vec<u8> {
        self.inner.domain_id()
    }
}

fn circuit<F: SerializableField + crate::core::algebra::AlgebraicField>(f: &F) -> Circuit<F> {
    let raw = RawCircuit {
        ninput: 3,
        npublic_input: 1,
        noutput: 1,
        logv: 0,
        subfield_boundary: 0,
        constants: vec![f.one(), f.mone()],
        layers: vec![Layer::new_compressed(
            3,
            2,
            vec![vec![
                TermDelta {
                    g: 0,
                    h: [0, 0],
                    k_index: 1,
                },
                TermDelta {
                    g: 0,
                    h: [1, 2],
                    k_index: 0,
                },
            ]],
            vec![0],
        )],
    };
    let id = compute_id(f, &raw);
    Circuit { raw, id }
}
pub(crate) fn exercise<
    const W: usize,
    F: ZkField<W>,
    D: EvaluationDomain<W, F>,
    SF: SubfieldV1<E = F::E>,
>(
    f: &F,
    domain: &D,
    sf: &SF,
) {
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let bounded = BoundedDomain {
        inner: domain,
        limit: config.k + config.n,
    };
    let context = ZkContext {
        f,
        domain: &bounded,
    };
    let public = vec![f.one()];
    let witness = vec![f.one(), f.one()];
    let p = ZkProver::new(circuit(f), config);
    let mut tp = Transcript::new(b"longfellow/v2/test");
    let mut rng = DeterministicRng::new(42);
    let (committed, prover_geometry) = p
        .commit(witness.to_vec(), &context, &mut tp, &mut rng)
        .unwrap();
    let proof = p.prove(&public, committed, &mut tp, &context).unwrap();
    let bytes = proof.write(&prover_geometry, f).unwrap();
    assert_eq!(&bytes[..4], b"LFV4");
    for old_marker in [b"ZNP1", b"ZNG1"] {
        let mut obsolete = bytes.clone();
        obsolete[..4].copy_from_slice(old_marker);
        assert!(ZkProof::read(&mut obsolete.as_slice(), &prover_geometry, f).is_err());
    }

    // Independently reconstruct the circuit, geometry, and decoded verifier proof.
    let mut v = ZkVerifier::new(circuit(f), config, &context).unwrap();
    let geometry = v.geometry();
    let mut input = bytes.as_slice();
    let decoded = ZkProof::read(&mut input, &geometry, f).unwrap();
    assert!(input.is_empty());
    let mut verify = |inputs: Vec<F::E>, candidate: &ZkProof<W, F>| {
        let mut tv = Transcript::new(b"longfellow/v2/test");
        v.receive_commitment(candidate, &mut tv);
        v.verify(&inputs, candidate, &mut tv, &context)
    };
    verify(public.clone(), &decoded).unwrap();
    {
        // The same witness/layout has the same commitment under a different
        // trusted circuit ID. Sumcheck still binds the ID and prevents replay.
        let mut other_circuit = circuit(f);
        other_circuit.id[0] ^= 1;
        let other_prover = ZkProver::new(other_circuit, config);
        let mut other_ts = Transcript::new(b"longfellow/v2/test");
        let (committed, _) = other_prover
            .commit(
                witness.to_vec(),
                &context,
                &mut other_ts,
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let other_proof = other_prover
            .prove(&public, committed, &mut other_ts, &context)
            .unwrap();
        assert_eq!(other_proof.com, proof.com);
        assert!(verify(public.clone(), &other_proof).is_err());

        let mut other_circuit = circuit(f);
        other_circuit.id[0] ^= 1;
        let mut other_verifier = ZkVerifier::new(other_circuit, config, &context).unwrap();
        let mut other_ts = Transcript::new(b"longfellow/v2/test");
        other_verifier.receive_commitment(&other_proof, &mut other_ts);
        other_verifier
            .verify(&public, &other_proof, &mut other_ts, &context)
            .unwrap();
    }
    let bad_public = vec![f.addf(&f.one(), &f.one())];
    assert!(verify(bad_public, &decoded).is_err());
    assert!(verify(vec![], &decoded).is_err());
    {
        let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
        f.add(&mut bad.com_proof.h[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
        f.add(&mut bad.sumcheck_proof.layers[0].claims[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        // The same circuit, field, and witness must succeed through the existing Ligero path.
        let legacy_context = crate::runtime::zk_v1::common::ZkContext {
            f,
            make_interpolator: domain,
        };
        let cfg = crate::runtime::ligero::LigeroConfig {
            rateinv: 2,
            nreq: 2,
            block_enc: 64,
        };
        let old = crate::runtime::zk_v1::ZkProver::new(circuit(f), cfg);
        let mut legacy_ts = Transcript::new(b"longfellow/v1/comparison");
        let (commit, geom) = old.commit(&witness, &legacy_context, &mut legacy_ts, &mut rng, sf);
        let legacy_proof = old
            .prove(
                public.clone(),
                witness.clone(),
                &commit,
                &mut legacy_ts,
                &legacy_context,
            )
            .unwrap();
        let legacy_bytes = legacy_proof.write(&geom, f, sf).unwrap();
        let verifier = crate::runtime::zk_v1::ZkVerifier::new(circuit(f), cfg);
        let mut tv = Transcript::new(b"longfellow/v1/comparison");
        verifier.recv_commitment(&legacy_proof, &mut tv, &legacy_context);
        verifier
            .verify(public, &legacy_proof, &mut tv, &legacy_context)
            .unwrap();
        assert!(ZkProof::read(&mut legacy_bytes.as_slice(), &geometry, f).is_err());
    }
}
#[test]
fn binary_zk_comparison() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
        subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let d = BinaryInterpolatorFactory::new(&f, &sf);
    exercise(&f, &d, &sf);
}
#[test]
fn prime_zk_comparison() {
    use crate::runtime::algebra::{
        fp2::Fp2Field,
        p256::{P256Field, P256Subfield},
        range_interpolation::QuadraticExtensionFftInterpolatorFactory,
        SupportsFFT,
    };
    let f = P256Field::new();
    let sf = P256Subfield::new(&f);
    let f2 = Fp2Field::new(&f);
    let d = QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    exercise(&f, &d, &sf);
}
#[test]
fn q256_zk_comparison() {
    use crate::runtime::algebra::{
        q256::Q256Field, range_interpolation::ScalarInterpolatorFactory,
    };
    let f = Q256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    let sf = FullField::<4, _>(&f);
    exercise(&f, &d, &sf);
}
#[cfg(feature = "experimental")]
#[test]
fn extension_zk_comparison() {
    use crate::runtime::algebra::{
        fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Subfield},
        range_interpolation::CrtInterpolatorFactory,
    };
    let f = RuntimeFp24Ext6::new();
    exercise(&f, &CrtInterpolatorFactory, &RuntimeFp24Subfield);
    let c = circuit(&f);
    use crate::runtime::proto::zk_v2::commitment_layout;
    let (_, nw, products) = commitment_layout(&c, &f);
    let select = |filter: fn(PolygeroConfig) -> bool| {
        crate::compile::polygero::tune_large_field_at_rate(
            4,
            nw,
            &products,
            f.serialized_size_bytes(),
            |config| filter(config) && config.can_interpolate(&CrtInterpolatorFactory),
        )
    };
    let config = select(|p| p.k == 992).unwrap();
    assert_eq!(
        (config.k, config.s, config.n, config.t),
        (992, 26, 3968, 131)
    );
    assert!(select(|_| false).is_none());
    let select_mldsa = |filter: fn(PolygeroConfig) -> bool| {
        crate::compile::polygero::tune_mldsa_128(nw, &products, |config| {
            filter(config) && config.can_interpolate(&CrtInterpolatorFactory)
        })
    };
    let mldsa = select_mldsa(|p| p.k == 992).unwrap();
    assert_eq!((mldsa.k, mldsa.s, mldsa.n, mldsa.t), (992, 24, 3968, 128));
    assert!(select_mldsa(|_| false).is_none());
    assert!(select_mldsa(|p| p.k == 993).is_none());
    // A public resource filter can only restrict the certified family.
    assert!(select(|p| p.k == 993).is_none());
}

#[test]
fn v2_rejects_legacy_boundary_before_sampling_or_transcript_changes() {
    use crate::{
        core::algebra::AlgebraicField,
        runtime::{
            algebra::{
                gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
                subfield_v1::BinarySubfield,
            },
            random::RandomEngine,
        },
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let context = ZkContext {
        f: &f,
        domain: &domain,
    };
    let config = PolygeroConfig {
        k: 8,
        s: 2,
        n: 64,
        t: 2,
    };
    let legacy = || {
        let mut c = circuit(&f);
        c.raw.subfield_boundary = 1;
        c
    };
    assert!(legacy().validate_v2().is_err());
    assert!(crate::runtime::sumcheck_v2::eval_circuit(vec![f.one(); 2], &legacy(), &f).is_err());
    assert!(ZkVerifier::new(legacy(), config, &context).is_err());
    #[cfg(feature = "experimental")]
    let p = ZkProver::new(legacy(), config);
    let mut ts = Transcript::new(b"boundary");
    let mut before = ts.clone();
    let mut rng = DeterministicRng::new(123);
    let state = rng.state;
    assert!(p
        .commit(vec![f.one()], &context, &mut ts, &mut rng)
        .is_err());
    assert_eq!(rng.state, state);
    assert_eq!(ts.u128(), before.u128());
}
