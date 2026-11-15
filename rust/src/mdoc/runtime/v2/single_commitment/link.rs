// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Pure foreign storage for every signature input and pad.
use super::{constants::QUOTIENT_BITS, encoding::SignatureEncoding, proof::ProofGeometry};
use crate::{
    core::proto::v2::Circuit,
    mdoc::{
        proto::layout,
        v2::{inputs::PublicInputs, ZkSpecStruct},
    },
    runtime::{
        algebra::{gf2_128::Gf2_128Field, p256::P256Field, range_interpolation::EvaluationDomain},
        v2::{
            foreign::{
                adapter::{p256::P256Mode, AdapterMode},
                reserved::ReservedSuffix,
            },
            proto::polygero::PolygeroConfig,
            transcript::{Header, Statement as TranscriptStatement},
            witness_selection::Field,
            zk::{
                coordinates::{AffineEncoding, CoordinateMap},
                joint::{CircuitParticipant, FrontendPart, JointParam},
                split::{pure::PureSplit, value_count},
                storage::Group,
                write_joint_geometry,
            },
        },
    },
};
pub(super) type Mode = P256Mode<QUOTIENT_BITS>;
type Fields<'a, D> = (Field<'a, Gf2_128Field, D>, ());
pub(super) struct Link<'a, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    pub(super) hash: &'a Circuit<Gf2_128Field>,
    pub(super) signature: &'a Circuit<P256Field>,
    pub(super) host_domain: &'a DH,
    pub(super) host: CircuitParticipant<Gf2_128Field>,
    pub(super) native: PureSplit<P256Field>,
    pub(super) map: CoordinateMap,
    #[cfg_attr(not(any(test, feature = "prover")), allow(dead_code))]
    pub(super) suffix: ReservedSuffix,
    pub(super) mode: Mode,
    pub(super) config: PolygeroConfig,
}
impl<'a, DH> Link<'a, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    pub(super) fn with_encoding<DS: EvaluationDomain<P256Field>>(
        spec: &ZkSpecStruct,
        signature: &'a Circuit<P256Field>,
        hash: &'a Circuit<Gf2_128Field>,
        domains: (&'a DH, &DS),
        encoding: SignatureEncoding,
    ) -> Result<Self, String> {
        let private_inputs = signature
            .raw
            .ninput
            .checked_sub(signature.raw.npublic_input)
            .ok_or("signature public prefix")?;
        if encoding == SignatureEncoding::AffineErs && private_inputs < layout::sig::DEVICE_ERS.end
        {
            return Err("signature private inputs do not cover the affine ERS layout".into());
        }
        let values = value_count(signature)?;

        let mut shared = vec![None; values];
        for (sig, hashed) in layout::SHARED {
            for (value, bit) in sig.zip(hashed) {
                *shared
                    .get_mut(value)
                    .ok_or("single signature shared index")? = Some(hash.raw.npublic_input + bit);
            }
        }
        let mut suffix = ReservedSuffix::new(hash.raw.ninput);
        let stored = shared
            .into_iter()
            .enumerate()
            .map(|(value, shared_bit)| {
                let affine = encoding == SignatureEncoding::AffineErs
                    && (layout::sig::ISSUER_ERS.contains(&value)
                        || layout::sig::DEVICE_ERS.contains(&value));
                let group = if let Some(bit) = shared_bit {
                    if bit < hash.raw.npublic_input || bit >= hash.raw.ninput {
                        return Err("single shared bit outside hash witness".into());
                    }
                    Group::new(bit, 1)?
                } else {
                    suffix.group(if affine { layout::sig::ERS_BITS } else { 256 })?
                };
                let coordinate = if affine {
                    AffineEncoding::new(layout::sig::ERS_SCALE, layout::sig::ERS_OFFSET)?
                } else {
                    AffineEncoding::IDENTITY
                };
                Ok((value, 0, group, coordinate))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let map = CoordinateMap::new_affine(values, 1, &stored)?;
        let mode = Mode::new(
            map.groups().map(|g| g.width()).collect(),
            hash.raw.npublic_input,
            &mut suffix,
        )?;
        let config = spec.polygero;
        let host = CircuitParticipant::new(
            &[hash, mode.fragment()],
            mode.virtual_inputs(),
            config,
            domains.0,
        )?;
        let native = PureSplit::new(signature, map.storage_map()?, config, domains.1)?;
        Ok(Self {
            hash,
            signature,
            host_domain: domains.0,
            host,
            native,
            map,
            suffix,
            mode,
            config,
        })
    }
    pub(super) fn param(&self) -> Result<JointParam<Fields<'_, DH>>, String> {
        JointParam::new((self.host.participant(self.host_domain)?, ()))
    }
    pub(super) fn geometry(&self) -> Result<ProofGeometry, String> {
        ProofGeometry::new(
            self.host.geometry(),
            self.native.geometry().sumcheck().clone(),
            self.config,
        )
    }
    pub(super) fn statement<'s>(
        &'s self,
        public: &'s PublicInputs<'_>,
    ) -> Result<Statement<'s, DH>, String> {
        Ok(Statement {
            identity: super::transcript::Identity::of(public.request()),
            link: self,
            host: FrontendPart::new(
                &self.host,
                &[self.hash, self.mode.fragment()],
                public.hash(),
            )?,
            native: FrontendPart::new(&self.native, &[self.signature], public.signature())?,
            geometry: self.geometry()?,
        })
    }
}

pub(super) struct Statement<'a, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    identity: super::transcript::Identity<'a>,
    link: &'a Link<'a, DH>,
    host: FrontendPart<'a, Gf2_128Field>,
    native: FrontendPart<'a, P256Field, PureSplit<P256Field>>,
    geometry: ProofGeometry,
}
impl<'a, DH> TranscriptStatement for Statement<'a, DH>
where DH: EvaluationDomain<Gf2_128Field>
{
    type Identity = super::transcript::Identity<'a>;
    fn identity(&self) -> &Self::Identity {
        &self.identity
    }
    fn write(&self, h: &mut Header<'_>) {
        self.host.write_circuits(h);
        self.native.write_circuits(h);
        self.host.write_layout(h);
        self.native.write_layout(h);
        self.link.map.write_layout(h);
        self.link.mode.write_layout(h);
        write_joint_geometry(h, self.geometry.config());
        self.host.write_public(h);
        self.native.write_public(h);
    }
}
cfg_prover! {mod prover;}
cfg_verifier! {mod verifier;}
