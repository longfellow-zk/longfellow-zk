// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{
    core::algebra::SupportsU64Conversions,
    mldsa::{
        proto::{shared_widths, MlDsaParams, CLAIMS},
        runtime::{binary::BinaryParticipant, reference::ConcreteInstance},
    },
    runtime::{
        algebra::{
            fp24_ext6::RuntimeFp24Ext6 as AF, range_interpolation::BinaryInterpolatorFactory,
        },
        random::PrivateRandom,
        v2::{
            foreign::adapter::exact::ExactMode,
            zk::{
                joint::{FrontendPart, JointParam},
                split::pure,
                write_joint_geometry,
            },
        },
    },
};
pub fn prove<P: MlDsaParams>(
    c: &Circuits,
    key: &[u8],
    instance: &ConcreteInstance<P>,
    context: &[u8],
    rng: &mut impl PrivateRandom,
) -> Result<Vec<u8>, String> {
    let f = Gf2_128Field::new();
    let af = AF::new();
    let domain = BinaryInterpolatorFactory::full_field(&f);
    let link = Link::new(c)?;
    let binary = link.host(c, &domain)?;
    let native = link.native(c, &CrtInterpolatorFactory)?;
    let params = JointParam::new((binary.participant(&domain)?, ()))?;
    let native_part = FrontendPart::new(&native, &[&c.arithmetic], &[])?;
    let npublic = c.binary.raw.npublic_input;
    let private_key = witness::key_witness::<P>(key, c.keccak)?;
    let mut bits = super::super::witness::binary_inputs(instance, c.keccak);
    if bits.len() != c.key_start {
        return Err("hidden key witness offset".into());
    }
    bits.extend(private_key);
    if bits.len() != c.base_private || npublic + bits.len() != c.binary.raw.ninput {
        return Err("hidden base witness shape".into());
    }
    // Native inputs: shared words read from the binary witness, then the
    // native-only polynomials.
    let widths = shared_widths::<P>();
    let mut offset = 0;
    let mut private = Vec::with_capacity(c.arithmetic.raw.ninput);
    for width in widths {
        let mut value = 0u64;
        for r in 0..width {
            let index = c
                .positions
                .get(offset + r)
                .ok_or("hidden native source positions")?;
            let bit = bits
                .get(index - npublic)
                .ok_or("hidden native source index")?;
            value |= u64::from(*bit) << r;
        }
        private.push(af.u64_to_element(value));
        offset += width;
    }
    for poly in instance
        .witness
        .approximation
        .iter()
        .chain(&instance.witness.ntt_z)
        .chain([&instance.witness.ntt_c])
    {
        private.extend(poly.iter().map(|&x| af.u64_to_element(x as u64)));
    }
    // Sample the native pads; every stored coordinate becomes a claim term.
    let state = native.prepare(private, rng)?;
    let values = link.map.term_values(state.values(), |x, coordinate| {
        let mut out = [0; CLAIMS];
        out[0] = x.coefficients()[coordinate];
        af.from_coefficients(out)
    })?;
    // Reserved suffix: native-only coordinates, then the quotient pads.
    let mut stored = Vec::with_capacity(link.native.width());
    for (g, v) in link.map.groups().zip(&values) {
        if g.start() < c.binary.raw.ninput {
            continue;
        }
        let value = v.coefficients()[0];
        if u64::from(value) >> g.width() != 0 {
            return Err("hidden source width".into());
        }
        stored.extend((0..g.width()).map(|r| value >> r & 1 != 0));
    }
    let pads = link.mode.sample_pads(rng);
    let mut reserved = link.suffix.witness();
    reserved.set(link.native, stored)?;
    link.mode.write_pads(&pads, &mut reserved)?;
    bits.extend(reserved.into_bits());
    let initial_transcript = transcript::start::<P>(c, context, |h| {
        binary.write_layout(h);
        native_part.write_layout(h);
        link.map.write_layout(h);
        link.mode.write_layout(h);
        write_joint_geometry(h, c.config);
    });
    let (host_state, cells) = binary.prepare(&bits, rng)?;
    let (mut joint, commitment, fingerprints) =
        params.commit((cells, ()), initial_transcript, rng)?;

    let (native_proof, pending) = pure::prover::prove(&mut joint.bound(&native_part), state)?;
    let linear = pending.claim.batch_linear(&mut joint.bound(&native_part))?;
    let claim = link.map.modular_claim(&linear, &basis(&af), &af)?;
    let (masked, leaves) =
        ExactMode::prove(&mut joint.bound(&link.mode), &claim, &values, pads, &af, &f)?;
    // Binary frontend: relation, key expansion and the fixed adapter fragment.
    let gamma = transcript::gamma(&mut joint.bound(&binary).transcript());

    let (proof, simd, statement) = BinaryParticipant::prove(
        &mut joint.bound(&binary),
        &c.binary,
        link.mode.fragment(),
        &gamma,
        bits,
        host_state,
        &leaves,
    )?;
    let statements = (statement, ());
    let (polygero, sealed_transcript) = joint.finish(statements)?;
    proto::Proof::<Gf2_128Field> {
        simd,
        native: native_proof,
        masked,
        commitment,
        fingerprints: fingerprints.0,
        binary: proof,
        polygero,
    }
    .write(
        &proto::geometry(c, binary.geometry(), &native),
        &f,
        sealed_transcript,
    )
    .map(|p| p.into_bytes())
}
