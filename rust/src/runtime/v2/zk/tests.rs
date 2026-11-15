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

use super::{ZkContext, ZkProver, ZkVerifier};
use crate::{
    core::proto::v2::quadratic_fixture,
    runtime::v2::{
        proto::{dual_packing::PackingProof, zk::ZkProof},
        sumcheck::circuit_geometry,
        zk::CircuitInput,
    },
};

#[test]
fn context_uses_its_domains_runtime_modulus() {
    use crate::runtime::algebra::{
        fp_generic::FpGenericField, limb::LIMBS_PER_U64,
        range_interpolation::ScalarInterpolatorFactory,
    };
    type Prime = FpGenericField<1, { LIMBS_PER_U64 }, { 3 * LIMBS_PER_U64 }>;
    let f17 = Prime::new_generic([17]);
    let f19 = Prime::new_generic([19]);
    let d17 = ScalarInterpolatorFactory::new(&f17, 16);
    let d19 = ScalarInterpolatorFactory::new(&f19, 16);
    let context17 = ZkContext::new(&d17);
    let context19 = ZkContext::new(&d19);
    assert!(std::ptr::eq(context17.field(), &f17));
    assert!(std::ptr::eq(context19.field(), &f19));
}
use crate::{
    core::{
        algebra::SerializableField,
        proto::v1::{compute_id, Circuit, Layer, RawCircuit, TermDelta},
    },
    runtime::{
        algebra::{
            range_interpolation::{EvaluationDomain, RangeInterpolatorFactory},
            RuntimeField, ZkField,
        },
        random::DeterministicRng,
        v2::{
            proto::polygero::PolygeroConfig,
            transcript::{Opened, Transcript},
        },
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
    fn field(&self) -> &F {
        self.inner.field()
    }
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
    quadratic_fixture(legacy_circuit(f), f)
}
fn exercise<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::packing::PackingField,
    D: EvaluationDomain<W, F>,
>(
    f: &F,
    domain: &D,
) -> crate::runtime::v2::transcript::Trace {
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
    let context = ZkContext::new(&bounded);
    use crate::{core::algebra::AlgebraicField, runtime::algebra::packing::PackingExtension};
    let extension = f.packing_extension();
    let base = extension.base();
    let public = vec![base.one()];
    let witness = vec![base.one(), base.one()];
    const CONTEXT: &[u8] = b"longfellow/v2/test";
    let p = ZkProver::new(circuit(f), config, &context).unwrap();
    let statement = p.statement(CONTEXT, &public).unwrap();
    let mut rng = DeterministicRng::new(42);
    let committed = p
        .commit(witness.to_vec(), &statement, &context, &mut rng)
        .unwrap();
    let prover_geometry = statement.geometry().clone();
    let source_circuit = circuit(f);
    let source_geometry = circuit_geometry(&[&source_circuit]).unwrap();
    let source = super::packing_commitment::PackingLayout::new(
        source_circuit.raw.ninput - source_circuit.raw.npublic_input,
        source_geometry.pad_count().unwrap(),
        extension.degree(),
    )
    .unwrap();
    assert_eq!(
        prover_geometry.circuit.com_geom.nw,
        source.witness_count + 2
    );
    let (proof, tp) = p.prove(committed, &context).unwrap();
    let encoded_proof = proof
        .write(&prover_geometry, f, tp.fork_for_test())
        .unwrap();
    let bytes = encoded_proof.as_bytes().to_vec();
    assert_eq!(&bytes[..4], b"LFV9");

    // Independently reconstruct the circuit, geometry, and decoded verifier proof.
    let v = ZkVerifier::new(circuit(f), config, &context).unwrap();
    let geometry = v.geometry();
    assert_eq!(geometry, prover_geometry);
    let vs = v.statement(CONTEXT, &public).unwrap();
    for old_marker in [b"LFV8", b"LFV4", b"LFV3", b"LFV2", b"ZNP1", b"ZNG1"] {
        let mut obsolete = bytes.clone();
        obsolete[..4].copy_from_slice(old_marker);
        let mut t = Transcript::new(&vs);
        assert!(ZkProof::read(&obsolete, &t.bound(vs.geometry()), f).is_err());
    }
    let mut session = Transcript::new(&vs);
    let decoded = ZkProof::read(&bytes, &session.bound(vs.geometry()), f).unwrap();
    // Every truncation and every extension fails at parse, before anything
    // is decoded (proto I3).
    for len in 0..bytes.len() {
        let cut = ZkProof::read(&bytes[..len], &session.bound(vs.geometry()), f);
        assert!(cut.is_err(), "length {len}");
    }
    for extra in 1..=64 {
        let mut longer = bytes.clone();
        longer.resize(bytes.len() + extra, 0);
        let read = ZkProof::read(&longer, &session.bound(vs.geometry()), f);
        assert!(read.is_err(), "{extra} extra bytes");
    }
    // The proof is exactly the length its geometry and frontier determine.
    let opening = decoded.com_proof.authentication_bytes();
    assert_eq!(
        bytes.len(),
        4 + 32
            + 2 * f.serialized_size_bytes()
            + prover_geometry
                .circuit
                .proof_len(f.serialized_size_bytes())
                .unwrap()
            + decoded.com_proof.bodies.0.payload_bytes(f)
            + opening.0
            + opening.1
            + 32
    );
    super::super::proto::tests::check_trace_matches_wire(
        encoded_proof.trace_for_test(),
        &bytes,
        4,
        bytes.len()
            - 32
            - decoded.com_proof.bodies.0.rows.len() * f.serialized_size_bytes()
            - opening.0
            - opening.1,
    );
    let complete = |encoded: &[u8], public: &[CircuitInput<F>]| -> Result<(), String> {
        let verifier = ZkVerifier::new(circuit(f), config, &context).map_err(|e| e.to_string())?;
        let statement = verifier
            .statement(CONTEXT, public)
            .map_err(|e| e.to_string())?;
        let mut session = Opened::new(&statement);
        let parsed = ZkProof::read(encoded, &session.bound(|s| s.geometry()), f)
            .map_err(|e| e.to_string())?;
        let verified = verifier
            .verify(session, parsed, &context)
            .map_err(|e| e.to_string())?;
        // Prover and verifier run one schedule (transcript I9).
        assert_eq!(verified.trace_for_test(), encoded_proof.trace_for_test());
        Ok(())
    };
    complete(&bytes, &public).unwrap();
    for offset in [4, bytes.len() / 2, bytes.len() - 1] {
        let mut changed = bytes.clone();
        changed[offset] ^= 1;
        assert!(complete(&changed, &public).is_err());
    }
    // Every truncation and every extension fails (proto I3).
    for len in (0..bytes.len()).step_by(97).chain([bytes.len() - 1]) {
        assert!(complete(&bytes[..len], &public).is_err(), "length {len}");
    }
    for extra in [1, 31, 32, 33] {
        let mut extended = bytes.clone();
        extended.extend(std::iter::repeat_n(0, extra));
        assert!(complete(&extended, &public).is_err(), "extended by {extra}");
    }
    let verify = |inputs: Vec<CircuitInput<F>>, candidate: &ZkProof<W, F>| {
        let statement = v.statement(CONTEXT, &inputs).map_err(|e| e.to_string())?;
        v.reduce(Opened::new(&statement), candidate, &context)
            .map_err(|e| e.to_string())
    };
    verify(public.clone(), &decoded).unwrap();
    for coordinate in 0..2 {
        let mut changed = (*decoded).clone();
        f.add(&mut changed.fingerprints.values[coordinate], &f.one());
        assert!(verify(public.clone(), &changed).is_err());
    }
    {
        // The same witness/layout has the same commitment under a different
        // trusted circuit ID. The statement binds the ID and prevents replay.
        let other_circuit = circuit(f);
        let mut id = other_circuit.id;
        id[0] ^= 1;
        let other_circuit =
            crate::core::proto::v2::Circuit::with_test_id(id, other_circuit.into_raw());
        let other_prover = ZkProver::new(other_circuit, config, &context).unwrap();
        let other_statement = other_prover.statement(CONTEXT, &public).unwrap();
        let committed = other_prover
            .commit(
                witness.to_vec(),
                &other_statement,
                &context,
                &mut DeterministicRng::new(42),
            )
            .unwrap();
        let (other_proof, _) = other_prover.prove(committed, &context).unwrap();
        assert_eq!(other_proof.com, proof.com);
        assert!(verify(public.clone(), &other_proof).is_err());

        let other_circuit = circuit(f);
        let mut id = other_circuit.id;
        id[0] ^= 1;
        let other_circuit =
            crate::core::proto::v2::Circuit::with_test_id(id, other_circuit.into_raw());
        let other_verifier = ZkVerifier::new(other_circuit, config, &context).unwrap();
        let other_statement = other_verifier.statement(CONTEXT, &public).unwrap();
        other_verifier
            .reduce(Opened::new(&other_statement), &other_proof, &context)
            .unwrap();
    }
    let bad_public = vec![base.zero()];
    assert!(verify(bad_public, &decoded).is_err());
    assert!(verify(vec![], &decoded).is_err());
    {
        let mut bad = ZkProof::read(&bytes, &session.bound(vs.geometry()), f)
            .unwrap()
            .clone();
        f.add(&mut bad.com_proof.bodies.0.h[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        let mut bad = ZkProof::read(&bytes, &session.bound(vs.geometry()), f)
            .unwrap()
            .clone();
        f.add(&mut bad.sumcheck_proof.layers[0].claims[0], &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    {
        let mut bad = ZkProof::read(&bytes, &session.bound(vs.geometry()), f)
            .unwrap()
            .clone();
        f.add(&mut bad.sumcheck_proof.layers[0].cross, &f.one());
        assert!(verify(public.clone(), &bad).is_err());
    }
    if let PackingProof::TraceZero { .. } = &decoded.packing {
        for change_first_response in [true, false] {
            let mut bad = ZkProof::read(&bytes, &session.bound(vs.geometry()), f)
                .unwrap()
                .clone();
            let PackingProof::TraceZero { u, a } = &mut bad.packing else {
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
        // A response off the trace-zero hyperplane must fail the trace check
        // itself. Compute the absolute trace independently of the library.
        let degree = 8 * f.serialized_size_bytes();
        let trace = |x: &F::E| {
            let mut sum = x.clone();
            let mut power = x.clone();
            for _ in 1..degree {
                power = f.mulf(&power, &power);
                f.add(&mut sum, &power);
            }
            sum
        };
        let off_hyperplane = (0..degree)
            .find_map(|bit| {
                let mut encoded = vec![0u8; f.serialized_size_bytes()];
                encoded[bit / 8] = 1 << (bit % 8);
                let x = f.bytes_to_element(&encoded).ok()?;
                (!f.is_zero(&trace(&x))).then_some(x)
            })
            .unwrap();
        let mut bad = ZkProof::read(&bytes, &session.bound(vs.geometry()), f)
            .unwrap()
            .clone();
        let PackingProof::TraceZero { u, .. } = &mut bad.packing else {
            unreachable!()
        };
        f.add(&mut u[0], &off_hyperplane);
        let Err(error) = verify(public.clone(), &bad) else {
            panic!("response with nonzero trace accepted");
        };
        let error = error.to_string();
        assert!(
            error.contains("packing response has nonzero trace"),
            "{error}"
        );
    }
    encoded_proof.trace_for_test().clone()
}
#[test]
fn binary_zk_comparison() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, range_interpolation::BinaryInterpolatorFactory,
    };
    let f = Gf2_128Field::new();
    let d = BinaryInterpolatorFactory::full_field(&f);
    let trace = exercise(&f, &d);
    // The full transcript of a small standalone proof: every node decodes
    // with the grammar and the registry alone, and its bytes are pinned.
    use crate::runtime::v2::proto::tests::{export_vectors, node_vector};
    let mut text = String::from(
        "## Standalone GF(2^128) proof: ZkStatement context \"longfellow/v2/test\", \
         profile (8, 2, 64, 2) in JointGeometry, the 3-input quadratic test circuit, \
         public input 1, DeterministicRng(42); every node of the full transcript\n\n",
    );
    for (i, node) in trace.nodes.iter().enumerate() {
        text += &node_vector("standalone", i, node);
    }
    export_vectors(&text);
    let all: Vec<u8> = trace.nodes.concat();
    assert_eq!(
        hex::encode(<sha2::Sha256 as sha2::Digest>::digest(&all)),
        "b21022c9aa67a38ab43c5b9da418b71dc1ef1fcc75d1290892535b4c7faf4fd6"
    );
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

mod layouts;

/// Prove `private` on `public` under `context`, on a transcript opened with
/// the proof's statement. Returns the proof, its geometry and the prover's
/// transcript.
#[allow(clippy::type_complexity)]
pub(super) fn prove_standalone<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::packing::PackingField,
    D: EvaluationDomain<W, F>,
>(
    prover: &ZkProver<W, F>,
    context: &[u8],
    public: &[CircuitInput<F>],
    private: Vec<CircuitInput<F>>,
    ctx: &ZkContext<'_, W, F, D>,
    rng: &mut impl crate::runtime::random::PrivateRandom,
) -> Result<
    (
        ZkProof<W, F>,
        crate::runtime::v2::proto::zk::ZkProofGeometry,
        Transcript,
    ),
    String,
> {
    let statement = prover.statement(context, public)?;
    let committed = prover.commit(private, &statement, ctx, rng)?;
    let (proof, t) = prover.prove(committed, ctx)?;
    Ok((proof, statement.geometry().clone(), t))
}
/// Reduce `proof` on a transcript opened with its statement.
pub(super) fn reduce_standalone<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::packing::PackingField,
    D: EvaluationDomain<W, F>,
>(
    verifier: &ZkVerifier<W, F>,
    context: &[u8],
    public: &[CircuitInput<F>],
    proof: &ZkProof<W, F>,
    ctx: &ZkContext<'_, W, F, D>,
) -> Result<Transcript, super::ZkVerificationError> {
    let statement = verifier.statement(context, public)?;
    verifier.reduce(Opened::new(&statement), proof, ctx)
}
/// Parse a complete proof against the geometry of its statement.
pub(super) fn read_standalone<
    const W: usize,
    F: ZkField<W> + crate::runtime::algebra::packing::PackingField,
>(
    verifier: &ZkVerifier<W, F>,
    context: &[u8],
    public: &[CircuitInput<F>],
    bytes: &[u8],
    f: &F,
) -> Result<ZkProof<W, F>, String> {
    let statement = verifier
        .statement(context, public)
        .map_err(|e| e.to_string())?;
    let mut t = Transcript::new(&statement);
    let proof =
        ZkProof::read(bytes, &t.bound(statement.geometry()), f).map_err(|e| e.to_string())?;
    Ok((*proof).clone())
}
