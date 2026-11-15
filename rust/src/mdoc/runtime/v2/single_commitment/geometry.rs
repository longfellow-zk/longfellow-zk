// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{encoding::SignatureEncoding, link::Link, ProofGeometry};
use crate::{
    core::proto::v2::Circuit,
    mdoc::v2::ZkSpecStruct,
    runtime::algebra::{
        fp2::Fp2Field,
        gf2_128::Gf2_128Field,
        p256::P256Field,
        range_interpolation::{
            BinaryInterpolatorFactory, QuadraticExtensionFftInterpolatorFactory,
        },
        SupportsFFT,
    },
};
/// Geometry of the single-commitment proof for the trusted ordinary archive.
pub fn proof_geometry(
    spec: &ZkSpecStruct,
    signature: &Circuit<P256Field>,
    hash: &Circuit<Gf2_128Field>,
) -> Result<ProofGeometry, String> {
    proof_geometry_with_encoding(spec, signature, hash, SignatureEncoding::default())
}
/// Geometry for an explicitly selected, transcript-bound signature encoding.
pub fn proof_geometry_with_encoding(
    spec: &ZkSpecStruct,
    signature: &Circuit<P256Field>,
    hash: &Circuit<Gf2_128Field>,
    encoding: SignatureEncoding,
) -> Result<ProofGeometry, String> {
    let p = P256Field::new();
    let f = Gf2_128Field::new();
    let extension = Fp2Field::new(&p);
    let prime = QuadraticExtensionFftInterpolatorFactory::new(
        &p,
        &extension,
        extension.omega(),
        extension.omega_order(),
    );
    let binary = BinaryInterpolatorFactory::full_field(&f);
    Link::with_encoding(spec, signature, hash, (&binary, &prime), encoding)?.geometry()
}
