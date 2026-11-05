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
        proto::v1::{compute_id, Circuit, Layer, RawCircuit, TermDelta},
    },
    runtime::{
        algebra::{EvaluationDomain, RangeInterpolatorFactory, RuntimeField, ZkField},
        polygero::PolygeroConfig,
        random::{DeterministicRng, Transcript},
    },
};

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

fn legacy_circuit<F: SerializableField + crate::core::algebra::AlgebraicField>(
    f: &F,
) -> Circuit<F> {
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
fn circuit<F: SerializableField + crate::core::algebra::AlgebraicField>(
    f: &F,
) -> crate::core::proto::v2::Circuit<F> {
    crate::core::proto::v2::quadratic_fixture(legacy_circuit(f), f)
}
pub(crate) fn exercise<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::PackingField,
    D: EvaluationDomain<W, F>,
>(
    f: &F,
    domain: &D,
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
    use crate::runtime::algebra::{AlgebraicField, PackingExtension};
    let extension = f.packing_extension();
    let base = extension.base();
    let public = vec![base.one()];
    let witness = vec![base.one(), base.one()];
    let p = ZkProver::new(circuit(f), config);
    let mut tp = Transcript::new(b"longfellow/v2/test");
    let mut rng = DeterministicRng::new(42);
    let (committed, prover_geometry) = p.commit(&witness, &context, &mut tp, &mut rng).unwrap();
    let proof = p
        .prove(&public, witness.clone(), committed, &mut tp, &context)
        .unwrap();
    let bytes = proof.write(&prover_geometry, f).unwrap();
    assert_eq!(&bytes[..4], b"LFV6");
    for old_marker in [b"LFV4", b"LFV3", b"LFV2", b"ZNP1", b"ZNG1"] {
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
    let mut verify = |inputs: Vec<crate::runtime::zk_v2::CircuitInput<F>>,
                      candidate: &ZkProof<W, F>| {
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
                &witness,
                &context,
                &mut other_ts,
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let other_proof = other_prover
            .prove(&public, witness.clone(), committed, &mut other_ts, &context)
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
    let bad_public = vec![base.zero()];
    assert!(verify(bad_public, &decoded).is_err());
    assert!(verify(vec![], &decoded).is_err());
    {
        let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
        f.add(&mut bad.com_proof.bodies.0.h[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
        f.add(&mut bad.sumcheck_proof.layers[0].claims[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
        f.add(&mut bad.sumcheck_proof.layers[0].cross, &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    if let crate::runtime::proto::dual_packing::PackingProof::TraceZero { .. } = &decoded.packing {
        for change_first_response in [true, false] {
            let mut bad = ZkProof::read(&mut bytes.as_slice(), &geometry, f).unwrap();
            let crate::runtime::proto::dual_packing::PackingProof::TraceZero { u, a } =
                &mut bad.packing
            else {
                unreachable!()
            };
            if change_first_response {
                // In GF128, Tr(1)=0. This alteration passes the trace test and
                // must still be rejected by authentication of the packing rows.
                f.add(&mut u[0], &f.one());
            } else {
                f.add(a, &f.one());
            }
            assert!(verify(public.clone(), &bad).is_err());
        }
    }
}
#[test]
fn binary_zk_comparison() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    exercise(&f, &d);
}
#[test]
fn prime_zk_comparison() {
    use crate::runtime::algebra::{
        fp2::Fp2Field, p256::P256Field,
        range_interpolation::QuadraticExtensionFftInterpolatorFactory, SupportsFFT,
    };
    let f = P256Field::new();
    let f2 = Fp2Field::new(&f);
    let d = QuadraticExtensionFftInterpolatorFactory::new(&f, &f2, f2.omega(), f2.omega_order());
    exercise(&f, &d);
}
#[test]
fn q256_zk_comparison() {
    use crate::runtime::algebra::{
        q256::Q256Field, range_interpolation::ScalarInterpolatorFactory,
    };
    let f = Q256Field::new();
    let d = ScalarInterpolatorFactory::new(&f, 128);
    exercise(&f, &d);
}
#[test]
fn extension_zk_comparison() {
    use crate::runtime::algebra::{
        fp24_ext6::RuntimeFp24Ext6, range_interpolation::CrtInterpolatorFactory,
    };
    let f = RuntimeFp24Ext6::new();
    exercise(&f, &CrtInterpolatorFactory);
    let c = circuit(&f);
    use crate::runtime::proto::zk_v2::commitment_layout;
    let (_, nw) = commitment_layout(&c, &f);
    let select = |filter: fn(PolygeroConfig) -> bool| {
        crate::compile::polygero::tune_large_field_at_rate(
            4,
            nw,
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
    // A public resource filter can only restrict the certified family.
    assert!(select(|p| p.k == 993).is_none());
}
