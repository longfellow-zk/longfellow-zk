// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::generic::*;
use crate::{
    core::algebra::{AlgebraicField, BareField, SerializableField},
    runtime::{
        algebra::{
            packing::{
                self, AmbientElement, BaseElement, FiniteField, IdentityExtension,
                PackingExtension, PackingParameters,
            },
            SupportsSampling,
        },
        random::{DeterministicRng, RandomEngine, Transcript},
    },
};

#[derive(Clone, Copy)]
struct Prime<const P: u8>;
impl<const P: u8> BareField for Prime<P> {
    type E = u8;
}
impl<const P: u8> AlgebraicField for Prime<P> {
    fn zero(&self) -> u8 {
        0
    }
    fn one(&self) -> u8 {
        1
    }
    fn add(&self, a: &mut u8, b: &u8) {
        *a = (*a + *b) % P;
    }
    fn sub(&self, a: &mut u8, b: &u8) {
        *a = (*a + P - *b) % P;
    }
    fn mul(&self, a: &mut u8, b: &u8) {
        *a = (*a * *b) % P;
    }
    fn invert(&self, a: &u8) -> u8 {
        assert_ne!(*a, 0);
        packing::pow_le(self, a, &[P - 2])
    }
}
impl<const P: u8> SupportsSampling for Prime<P> {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> u8 {
        let mask = u8::MAX >> (P - 1).leading_zeros();
        loop {
            let bytes = rng(1);
            assert_eq!(bytes.len(), 1);
            let n = bytes[0] & mask;
            if n < P {
                return n;
            }
        }
    }
}
impl<const P: u8> FiniteField for Prime<P> {
    fn order_le(&self) -> Vec<u8> {
        vec![P]
    }
    fn field_id(&self) -> Vec<u8> {
        vec![b'p', P]
    }
}
impl<const P: u8> SerializableField for Prime<P> {
    fn is_binary(&self) -> bool {
        P == 2
    }
    fn serialized_size_bytes(&self) -> usize {
        1
    }
    fn to_bytes_into(&self, x: &u8, b: &mut [u8]) {
        b[0] = *x;
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<u8, String> {
        match b {
            [n] if *n < P => Ok(*n),
            _ => Err("prime codec".into()),
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        vec![P - 1]
    }
}
/// t²=A*t+B; instantiate GF4, GF9 and GF25 below.
#[derive(Clone, Copy)]
struct Quad<const P: u8, const A: u8, const B: u8>;
impl<const P: u8, const A: u8, const B: u8> BareField for Quad<P, A, B> {
    type E = [u8; 2];
}
impl<const P: u8, const A: u8, const B: u8> AlgebraicField for Quad<P, A, B> {
    fn zero(&self) -> Self::E {
        [0, 0]
    }
    fn one(&self) -> Self::E {
        [1, 0]
    }
    fn add(&self, a: &mut Self::E, b: &Self::E) {
        for i in 0..2 {
            Prime::<P>.add(&mut a[i], &b[i]);
        }
    }
    fn sub(&self, a: &mut Self::E, b: &Self::E) {
        for i in 0..2 {
            Prime::<P>.sub(&mut a[i], &b[i]);
        }
    }
    fn mul(&self, a: &mut Self::E, b: &Self::E) {
        let [x, y] = *a;
        *a = [
            (x * b[0] + B * y * b[1]) % P,
            (x * b[1] + y * b[0] + A * y * b[1]) % P,
        ];
    }
    fn invert(&self, a: &Self::E) -> Self::E {
        assert_ne!(*a, [0, 0]);
        packing::pow_le(self, a, &[P * P - 2])
    }
}
impl<const P: u8, const A: u8, const B: u8> SupportsSampling for Quad<P, A, B> {
    fn sample<R: FnMut(usize) -> Vec<u8>>(&self, mut rng: R) -> Self::E {
        let mask = u8::MAX >> (P * P - 1).leading_zeros();
        loop {
            let bytes = rng(1);
            assert_eq!(bytes.len(), 1);
            let n = bytes[0] & mask;
            if n < P * P {
                return [n % P, n / P];
            }
        }
    }
}
impl<const P: u8, const A: u8, const B: u8> FiniteField for Quad<P, A, B> {
    fn order_le(&self) -> Vec<u8> {
        vec![P * P]
    }
    fn field_id(&self) -> Vec<u8> {
        vec![b'q', P, A, B]
    }
}
impl<const P: u8, const A: u8, const B: u8> SerializableField for Quad<P, A, B> {
    fn is_binary(&self) -> bool {
        P == 2
    }
    fn serialized_size_bytes(&self) -> usize {
        1
    }
    fn to_bytes_into(&self, x: &Self::E, b: &mut [u8]) {
        b[0] = x[0] + P * x[1];
    }
    fn bytes_to_element(&self, b: &[u8]) -> Result<Self::E, String> {
        match b {
            [n] if *n < P * P => Ok([*n % P, *n / P]),
            _ => Err("quad codec".into()),
        }
    }
    fn serialized_mone(&self) -> Vec<u8> {
        vec![P - 1]
    }
}
impl<const P: u8, const A: u8, const B: u8> PackingExtension for Quad<P, A, B> {
    type Base = Prime<P>;
    type Ambient = Self;
    fn base(&self) -> &Prime<P> {
        &Prime::<P>
    }
    fn degree(&self) -> usize {
        2
    }
    fn embedding_id(&self) -> Vec<u8> {
        b"constant/v1".to_vec()
    }
    fn embed(&self, _: &Self, x: &u8) -> [u8; 2] {
        [*x, 0]
    }
    fn native_basis(&self, _: &Self) -> Vec<[u8; 2]> {
        vec![[1, 0], [0, 1]]
    }
    fn coordinates_into(&self, _: &Self, x: &[u8; 2], out: &mut [u8]) {
        out.copy_from_slice(x);
    }
}
fn laws<X: PackingExtension>(p: &PackingParameters<X>, values: &[BaseElement<X>]) {
    let f = p.field();
    let b = p.extension().base();
    let m = p.degree();
    for i in 0..m {
        for j in 0..m {
            assert_eq!(
                p.trace(&f.mulf(&p.basis()[i], &p.dual()[j])),
                if i == j { f.one() } else { f.zero() }
            );
        }
    }
    let words = p.pack(values).unwrap();
    assert_eq!(p.unpack(&words, values.len()).unwrap(), values);
    for word in words {
        let mut orbit = word.clone();
        for _ in 0..m {
            orbit = p.frobenius(&orbit);
        }
        assert_eq!(orbit, word);
        assert_eq!(p.trace(&p.frobenius(&word)), p.trace(&word));
    }
    for x in values {
        let embed = p.extension().embed(f, x);
        assert_eq!(p.extension().extract_base(f, &embed).unwrap(), *x);
        assert_eq!(p.frobenius(&embed), embed);
        assert_eq!(
            p.extension().embed(f, &b.addf(x, x)),
            f.addf(&embed, &embed)
        );
    }
}
fn roundtrip<X: PackingExtension>(
    p: &PackingParameters<X>,
    values: &[BaseElement<X>],
    mut sample: impl FnMut() -> AmbientElement<X>,
) where
    X::Ambient: SerializableField,
{
    let f = p.field();
    let weights = (0..values.len()).map(|_| sample()).collect::<Vec<_>>();
    let aux = vec![sample(), sample()];
    let terms = vec![(0, sample()), (1, sample()), (0, sample())];
    let mut constant = f.zero();
    for (w, x) in weights.iter().zip(values) {
        f.add(&mut constant, &f.mulf(w, &p.extension().embed(f, x)));
    }
    for (i, k) in &terms {
        f.sub(&mut constant, &f.mulf(k, &aux[*i]));
    }
    let claim = SourceClaim {
        weights,
        rhs: Affine { constant, terms },
        auxiliary_count: 2,
    };
    let masks = PackingMasks::sample(p, &mut sample);
    let cells = masks.cells().to_vec();
    let mut tp = Transcript::new(b"generic/test");
    let mut tv = tp.clone();
    let (proof, rows) = prove(
        p,
        &claim,
        values,
        &aux,
        masks,
        b"commitment context",
        &mut tp,
    )
    .unwrap();
    assert_eq!(
        verify(p, &claim, &proof, b"commitment context", &mut tv).unwrap(),
        rows
    );
    assert_eq!(tp.u128(), tv.u128());
    for row in &rows {
        assert!(f.is_zero(
            &row.residual(&p.pack(values).unwrap(), &aux, &cells, f)
                .unwrap()
        ));
    }
    let bytes = proof.write(p).unwrap();
    let mut rest = bytes.as_slice();
    let decoded = p.read_proof(&mut rest).unwrap();
    assert_eq!(decoded, proof);
    assert!(rest.is_empty());
    for len in 0..bytes.len() {
        assert!(p.read_proof(&mut &bytes[..len]).is_err());
    }
    if !bytes.is_empty() {
        let mut wrong = bytes.clone();
        wrong[0] ^= 1;
        assert!(p.read_proof(&mut wrong.as_slice()).is_err());
        let mut bad = proof.clone();
        let PackingProof::TraceZero { u, .. } = &mut bad else {
            unreachable!()
        };
        u.pop();
        assert!(bad.write(p).is_err());
        assert!(verify(
            p,
            &claim,
            &bad,
            b"commitment context",
            &mut Transcript::new(b"generic/test")
        )
        .is_err());
        let different = verify(
            p,
            &claim,
            &proof,
            b"other context",
            &mut Transcript::new(b"generic/test"),
        )
        .unwrap();
        assert_ne!(rows, different);
    }
}
#[test]
fn odd_characteristic_nonunit_basis_and_characteristic_dividing_degree() {
    let p = PackingParameters::new(Quad::<3, 0, 2>, Quad::<3, 0, 2>).unwrap();
    laws(&p, &[1, 2, 0, 2, 1]);
    let mut rng = DeterministicRng::new(17);
    roundtrip(&p, &[1, 2, 0, 2, 1], || {
        [rng.bytes(1)[0] % 3, rng.bytes(1)[0] % 3]
    });
    let changed =
        PackingParameters::with_basis(Quad::<5, 0, 2>, Quad::<5, 0, 2>, vec![[2, 1], [1, 1]])
            .unwrap();
    laws(&changed, &[1, 3, 4]);
    roundtrip(&changed, &[1, 3, 4], || {
        [rng.bytes(1)[0] % 5, rng.bytes(1)[0] % 5]
    });
    let even = PackingParameters::new(Quad::<2, 1, 1>, Quad::<2, 1, 1>).unwrap();
    assert_eq!(even.trace(&[1, 0]), [0, 0]);
    laws(&even, &[1, 0, 1]);
    roundtrip(&even, &[1, 0, 1], || {
        [rng.bytes(1)[0] % 2, rng.bytes(1)[0] % 2]
    });
    assert!(
        PackingParameters::with_basis(Quad::<3, 0, 2>, Quad::<3, 0, 2>, vec![[1, 0], [2, 0]])
            .is_err()
    );
}
#[test]
fn identity_has_no_masks_messages_or_challenges_even_with_nonunit_basis() {
    let p = PackingParameters::with_basis(Prime::<5>, IdentityExtension::new(Prime::<5>), vec![3])
        .unwrap();
    laws(&p, &[1, 4, 2]);
    let mut calls = 0;
    let masks = PackingMasks::sample(&p, || {
        calls += 1;
        0
    });
    assert_eq!(calls, 0);
    assert!(masks.cells().is_empty());
    let c = SourceClaim {
        weights: vec![2, 4, 1],
        rhs: Affine {
            constant: 0,
            terms: vec![],
        },
        auxiliary_count: 0,
    };
    let mut ts = Transcript::new(b"identity");
    let mut before = ts.clone();
    let (proof, rows) = prove(&p, &c, &[1, 4, 2], &[], masks, b"ignored", &mut ts).unwrap();
    assert_eq!(proof, PackingProof::Direct);
    assert_eq!(rows.len(), 1);
    assert_eq!(ts.u128(), before.u128());
    let residual = rows[0]
        .residual(&p.pack(&[1, 4, 2]).unwrap(), &[], &[], p.field())
        .unwrap();
    assert_eq!(residual, 0);
    assert!(proof.write(&p).unwrap().is_empty());
    assert!(PackingMasks::from_cells(&p, vec![0]).is_err());
}
#[test]
fn exhaustive_false_claim_error_in_gf9_includes_arbitrary_b() {
    let p = PackingParameters::new(Quad::<3, 0, 2>, Quad::<3, 0, 2>).unwrap();
    let f = p.field();
    let all = (0..9).map(|n| [n % 3, n / 3]).collect::<Vec<_>>();
    let zero_trace = all
        .iter()
        .copied()
        .filter(|x| p.trace(x) == f.zero())
        .collect::<Vec<_>>();
    assert_eq!(zero_trace.len(), 3);
    let c = SourceClaim {
        weights: vec![[1, 0], [0, 1]],
        rhs: Affine {
            constant: [0, 0],
            terms: vec![],
        },
        auxiliary_count: 0,
    };
    let words = p.pack(&[1, 2]).unwrap();
    let free = [2, 1];
    let t0 = f.mulf(&p.basis()[1], &free);
    let r = [1, 1];
    for b in &all {
        let cells = vec![free, r, *b];
        for u0 in &zero_trace {
            for u1 in &zero_trace {
                let mut successes = 0;
                for d0 in &all {
                    for d1 in &all {
                        let a = f.addf(&r, &f.addf(&f.mulf(d0, &t0), &f.mulf(d1, &free)));
                        let proof = PackingProof::TraceZero {
                            u: vec![*u0, *u1],
                            a,
                        };
                        let rows = reconstruct(&p, &c, &proof, &[*d0, *d1]).unwrap();
                        if rows
                            .iter()
                            .all(|row| row.residual(&words, &[], &cells, f).unwrap() == f.zero())
                        {
                            successes += 1;
                        }
                    }
                }
                assert!(successes <= 9, "{successes}/81, b={b:?}");
            }
        }
    }
}
#[test]
fn binary128_generic_matches_specialized_messages_transcript_and_equations() {
    use crate::{
        core::bits::PackedBits,
        runtime::algebra::{
            gf2_128::{Gf2_128 as V, Gf2_128Field as F},
            packing::binary::Binary128Extension,
        },
    };
    let f = F::new();
    let p = PackingParameters::new(f.clone(), Binary128Extension).unwrap();
    let basis = super::field::PolynomialBasis128::new(&f);
    let mut rng = DeterministicRng::new(998);
    let values = (0..137).map(|_| rng.u128() & 1 != 0).collect::<Vec<_>>();
    let bits: PackedBits = values.iter().copied().collect();
    laws(&p, &values);
    let weights = (0..values.len())
        .map(|_| V::from(rng.u128()))
        .collect::<Vec<_>>();
    let target = weights.iter().zip(&values).fold(
        f.zero(),
        |acc, (w, b)| if *b { f.addf(&acc, w) } else { acc },
    );
    let claim = SourceClaim {
        weights: weights.clone(),
        rhs: Affine {
            constant: target,
            terms: vec![],
        },
        auxiliary_count: 0,
    };
    let old = super::BitLinearClaim {
        weights,
        rhs: super::AffineClaim {
            constant: target,
            terms: vec![],
        },
        auxiliary_count: 0,
    };
    let masks = super::prover::DualPackingMaskValues::sample(&mut rng, &f);
    let cells = masks.cells();
    let generic = PackingMasks::from_cells(&p, cells.to_vec()).unwrap();
    let mut tp = Transcript::new(b"same");
    let mut tg = tp.clone();
    let (proof, rows) =
        super::prover::reduce(&basis, &old, &bits, &[], masks, b"root", &mut tp, &f).unwrap();
    let (gproof, grows) = prove(&p, &claim, &values, &[], generic, b"root", &mut tg).unwrap();
    assert_eq!(
        gproof,
        PackingProof::TraceZero {
            u: proof.u.to_vec(),
            a: proof.a
        }
    );
    assert_eq!(tp.u128(), tg.u128());
    let mut bytes = Vec::new();
    proof.write_to_buf(&mut bytes);
    assert_eq!(gproof.write(&p).unwrap(), bytes);
    let words = p.pack(&values).unwrap();
    for i in 0..2 {
        assert_eq!(
            rows[i].residual(&words, &[], &cells, &f).unwrap(),
            grows[i].residual(&words, &[], &cells, &f).unwrap()
        );
    }
}
#[test]
fn gf128_over_gf256_packs_non_boolean_coordinates() {
    use crate::runtime::algebra::{
        gf2_128::{Gf2_128 as V, Gf2_128Field},
        packing::binary::Binary128Over256,
    };
    let e = Binary128Over256::new();
    let values = (0..33)
        .map(|i| e.base().element((i * 7 + 3) as u8))
        .collect::<Vec<_>>();
    let p = PackingParameters::new(Gf2_128Field::new(), e).unwrap();
    laws(&p, &values);
    let mut rng = DeterministicRng::new(889);
    roundtrip(&p, &values, || V::from(rng.u128()));
}
#[cfg(feature = "experimental")]
#[test]
fn sextic_prime_extension() {
    use crate::runtime::algebra::{fp24_ext6::RuntimeFp24Ext6, packing::prime24::Prime24Extension};
    let f = RuntimeFp24Ext6::new();
    let p = PackingParameters::new(f, Prime24Extension).unwrap();
    let values = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    laws(&p, &values);
    let mut rng = DeterministicRng::new(123);
    roundtrip(&p, &values, || {
        f.from_coefficients(std::array::from_fn(|_| (rng.u128() % 8_380_417) as u32))
    });
}

fn authenticate<
    const W: usize,
    X: PackingExtension,
    D: crate::runtime::algebra::EvaluationDomain<W, X::Ambient>,
>(
    p: &PackingParameters<X>,
    domain: &D,
    values: &[BaseElement<X>],
) where
    X::Ambient: crate::runtime::algebra::RuntimeField<W>
        + crate::runtime::algebra::SupportsSampling
        + SerializableField,
{
    use crate::runtime::{
        polygero::{
            PolygeroConfig, PolygeroLinearTerm, PolygeroParam, PolygeroProver, PolygeroVerifier,
        },
        proto::Digest,
    };
    let f = p.field();
    let mut rng = DeterministicRng::new(99876);
    let packed = p.pack(values).unwrap();
    let aux = vec![rng.elt_field(f)];
    let masks = PackingMasks::sample(p, || rng.elt_field(f));
    let mut witness = packed.clone();
    witness.extend_from_slice(&aux);
    witness.extend_from_slice(masks.cells());
    let param = PolygeroParam::try_new(
        witness.len(),
        &[],
        PolygeroConfig {
            k: 8,
            s: 2,
            n: 64,
            t: 2,
        },
        domain,
        f,
    )
    .unwrap();
    let mut verifier = PolygeroVerifier::new(param.clone());
    let mut tp = Transcript::new(b"generic/backend");
    let mut tv = tp.clone();
    let (prover, root) =
        PolygeroProver::commit(witness, param, &mut tp, domain, &mut rng, f).unwrap();
    verifier.receive_commitment(&root, &mut tv);
    let weights = (0..values.len())
        .map(|_| rng.elt_field(f))
        .collect::<Vec<_>>();
    let auxiliary_coefficient = rng.elt_field(f);
    let mut constant = f.neg(&f.mulf(&auxiliary_coefficient, &aux[0]));
    for (w, x) in weights.iter().zip(values) {
        f.add(&mut constant, &f.mulf(w, &p.extension().embed(f, x)));
    }
    let claim = SourceClaim {
        weights,
        rhs: Affine {
            constant,
            terms: vec![(0, auxiliary_coefficient)],
        },
        auxiliary_count: 1,
    };
    let (proof, equations) =
        prove(p, &claim, values, &aux, masks, &root.root.data, &mut tp).unwrap();
    assert_eq!(
        verify(p, &claim, &proof, &root.root.data, &mut tv).unwrap(),
        equations
    );
    let mut terms = Vec::new();
    for (c, row) in equations.iter().enumerate() {
        for (w, k) in row.words.iter().enumerate() {
            terms.push(PolygeroLinearTerm { c, w, k: k.clone() });
        }
        for (i, k) in &row.auxiliary {
            terms.push(PolygeroLinearTerm {
                c,
                w: packed.len() + i,
                k: k.clone(),
            });
        }
        for (i, k) in row.masks.iter().enumerate() {
            terms.push(PolygeroLinearTerm {
                c,
                w: packed.len() + aux.len() + i,
                k: k.clone(),
            });
        }
    }
    let constants = equations
        .iter()
        .map(|e| e.constant.clone())
        .collect::<Vec<_>>();
    let statement = Digest {
        data: tp.bytes(32).try_into().unwrap(),
    };
    assert_eq!(statement.data, tv.bytes(32).as_slice());
    let backend = prover
        .prove(&constants, &mut tp, &terms, &statement, domain, f)
        .unwrap();
    verifier
        .verify(
            &constants, &root, &backend, &terms, &statement, &mut tv, domain, f,
        )
        .unwrap();
}
#[test]
fn generic_equations_authenticate_against_the_original_polygero_commitment() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field, packing::binary::Binary128Over256,
        range_interpolation::BinaryInterpolatorFactory, subfield_v1::BinarySubfield,
    };
    let f = Gf2_128Field::new();
    let sf = BinarySubfield::new(&crate::core::algebra::proto::GF2_16_BASIS_V1);
    let domain = BinaryInterpolatorFactory::new(&f, &sf);
    let extension = Binary128Over256::new();
    let values = (0..19)
        .map(|i| extension.base().element((i * 11) as u8))
        .collect::<Vec<_>>();
    let p = PackingParameters::new(f.clone(), extension).unwrap();
    authenticate(&p, &domain, &values);
    let identity = PackingParameters::new(f.clone(), IdentityExtension::new(f.clone())).unwrap();
    authenticate(&identity, &domain, &[f.one(), f.mone()]);
    #[cfg(feature = "experimental")]
    {
        use crate::runtime::algebra::{
            fp24_ext6::RuntimeFp24Ext6, packing::prime24::Prime24Extension,
            range_interpolation::CrtInterpolatorFactory,
        };
        let sextic_parameters = PackingParameters::new(RuntimeFp24Ext6, Prime24Extension).unwrap();
        authenticate(
            &sextic_parameters,
            &CrtInterpolatorFactory,
            &[1, 2, 3, 4, 5, 6, 7],
        );
    }
}
#[test]
fn field_orders_and_exponents_are_not_machine_words() {
    use crate::runtime::algebra::{p256::P256Field, packing::PackingField};
    let f = P256Field::new();
    let mut exponent = f.order_le();
    assert!(exponent.len() > std::mem::size_of::<usize>());
    for byte in &mut exponent {
        if *byte != 0 {
            *byte -= 1;
            break;
        }
        *byte = 255;
    }
    let x = f.addf(&f.one(), &f.one());
    assert_eq!(packing::pow_le(&f, &x, &exponent), f.one());
    let extension = f.packing_extension();
    let p = PackingParameters::new(f, extension).unwrap();
    assert_eq!(p.degree(), 1);
    assert_eq!(mask_cell_count(p.degree()), 0);
}

#[test]
fn sparse_prime_codec_samples_uniformly_without_padding_grinding() {
    use crate::runtime::algebra::{
        fp_generic::FpGenericField, packing::PackingField, LIMBS_PER_U64,
    };
    struct NonCloneBrand;
    type SmallPrime =
        FpGenericField<1, { LIMBS_PER_U64 }, { 2 * LIMBS_PER_U64 + 1 }, NonCloneBrand>;
    let field = SmallPrime::new_generic([1009]);
    let mut rng = DeterministicRng::new(217);
    let mut calls = 0;
    for _ in 0..100 {
        let x = field.sample(|n| {
            calls += 1;
            rng.bytes(n)
        });
        assert!(field.bytes_to_element(&field.to_bytes(&x)).is_ok());
    }
    assert!(calls < 200);
    let adapter = field.packing_extension();
    assert_eq!(PackingParameters::new(field, adapter).unwrap().degree(), 1);
}

#[test]
fn protocol_and_v1_subfield_paths_use_the_field_sampler() {
    use crate::runtime::algebra::{
        gf2_128::Gf2_128Field,
        p256::{P256Field, P256Subfield},
        q256::Q256Field,
        RuntimeField, SubfieldV1,
    };
    fn compare<const W: usize, F: FiniteField + RuntimeField<W>>(f: &F) {
        let mut direct = DeterministicRng::new(21937);
        let mut protocol = DeterministicRng::new(21937);
        for _ in 0..64 {
            assert_eq!(f.sample(|n| direct.bytes(n)), protocol.elt_field(f));
        }
        assert_eq!(direct.state, protocol.state);
    }
    compare(&Gf2_128Field::new());
    compare(&P256Field::new());
    compare(&Q256Field::new());
    let field = P256Field::new();
    let sf = P256Subfield::new(&field);
    let mut direct = DeterministicRng::new(77);
    let mut legacy = DeterministicRng::new(77);
    for _ in 0..64 {
        assert_eq!(
            field.sample(|n| direct.bytes(n)),
            sf.sample(|n| legacy.bytes(n))
        );
    }
    assert_eq!(direct.state, legacy.state);
    #[cfg(feature = "experimental")]
    {
        use crate::runtime::algebra::{
            fp24_ext6::{RuntimeFp24Ext6, RuntimeFp24Subfield},
            packing::prime24::Prime24,
        };
        compare(&RuntimeFp24Ext6);
        let mut prime_rng = DeterministicRng::new(771);
        let mut subfield_rng = DeterministicRng::new(771);
        for _ in 0..64 {
            assert_eq!(
                RuntimeFp24Subfield
                    .sample(|n| subfield_rng.bytes(n))
                    .coefficients()[0],
                Prime24.sample(|n| prime_rng.bytes(n))
            );
        }
        assert_eq!(prime_rng.state, subfield_rng.state);
    }
}
#[test]
fn distinguished_mask_coordinate_must_complement_the_base_field() {
    use std::collections::BTreeSet;
    let f = Quad::<3, 0, 2>;
    let x = [0, 1];
    // With the swapped basis [x,1], witnesses (0,0) and (1,2) both
    // satisfy the public claim x_0+x_1=0, but their U supports are disjoint.
    let as_image = |t: &[u8; 2]| f.subf(&packing::pow_le(&f, t, &[3]), t);
    let mut zero = BTreeSet::new();
    let mut other = BTreeSet::new();
    let mut admissible = BTreeSet::new();
    for a in 0..3 {
        for b in 0..3 {
            let t = [a, b];
            let v = as_image(&t);
            zero.insert((v, v));
            other.insert((v, f.addf(&v, &x)));
            admissible.insert((as_image(&f.mulf(&x, &t)), v));
        }
    }
    assert_eq!(zero.len(), 3);
    assert!(zero.is_disjoint(&other));
    assert_eq!(admissible.len(), 9);
    assert!(PackingParameters::with_basis(f, f, vec![x, f.one()]).is_err());
    let good = PackingParameters::new(f, f).unwrap();
    assert_eq!(good.basis(), &[f.one(), x]);
}
