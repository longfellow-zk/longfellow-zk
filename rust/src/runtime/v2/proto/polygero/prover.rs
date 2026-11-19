// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The prover's encoding of the Polygero wire format.
use std::io::{Error, Result};

use super::{
    super::util::write_elt_field, codec::validate_opening, FieldProof, JointPolygeroProof,
    PolygeroGeometry,
};
use crate::core::algebra::SerializableField;

impl<E> FieldProof<E> {
    /// The interactive response: H, then Z.
    pub(crate) fn write_response<F: SerializableField<E = E>>(
        &self,
        out: &mut Vec<u8>,
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.validate(g)?;
        for x in self.h.iter().chain(&self.z) {
            write_elt_field(out, x, f);
        }
        Ok(())
    }
    /// The terminal rows u, m, witness, f*, t values each in query order.
    pub(crate) fn write_rows<F: SerializableField<E = E>>(
        &self,
        out: &mut Vec<u8>,
        g: &PolygeroGeometry,
        f: &F,
    ) -> Result<()> {
        self.validate(g)?;
        for x in &self.rows {
            write_elt_field(out, x, f);
        }
        Ok(())
    }
}
impl<B> JointPolygeroProof<B> {
    /// Write each field's response, then each field's rows, then the nonces,
    /// then the frontier (its count, then its digests): the last field of
    /// every body.
    pub(crate) fn write_to_buf<E: From<Error>>(
        &self,
        out: &mut Vec<u8>,
        t: usize,
        n: usize,
        write_responses: impl FnOnce(&B, &mut Vec<u8>) -> std::result::Result<(), E>,
        write_rows: impl FnOnce(&B, &mut Vec<u8>) -> std::result::Result<(), E>,
    ) -> std::result::Result<(), E> {
        validate_opening(&self.opening, t, n)?;
        write_responses(&self.bodies, out)?;
        write_rows(&self.bodies, out)?;
        self.opening.write_nonces(out);
        self.opening.write_path(out);
        Ok(())
    }
}
