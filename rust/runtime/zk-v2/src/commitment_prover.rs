// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{CommitmentStatement, PackingCommitment};
use crate::runtime::{
    algebra::{EvaluationDomain, PackingExtension, ZkField},
    dual_packing::generic::{self, PackingMasks, PackingProof},
    polygero::{PolygeroParam, PolygeroProver},
    proto::polygero::{PolygeroCommitment, PolygeroProof},
    random::{RandomEngine, Transcript},
};
/// Validated logical inputs and their packed commitment prefix, prepared before sampling.
pub(in crate::runtime::zk_v2) struct PreparedInputs<E> {
    logical: Vec<E>,
    packed: Vec<E>,
}
pub(in crate::runtime::zk_v2) struct CommitmentState<
    const W: usize,
    F: ZkField<W>,
    X: PackingExtension<Ambient = F>,
> {
    pub backend: PackingCommitment<F, X>,
    pub private: Vec<F::E>,
    pub commitment: PolygeroCommitment,
    words: Vec<F::E>,
    suffix: Vec<F::E>,
    masks: PackingMasks<F::E>,
    polygero: PolygeroProver<W, F>,
}
impl<F: crate::runtime::algebra::PackingField, X: PackingExtension<Ambient = F>>
    PackingCommitment<F, X>
{
    pub fn prepare_inputs(&self, logical: Vec<F::E>) -> Result<PreparedInputs<F::E>, String> {
        if logical.len() != self.layout.private_inputs {
            return Err("witness length mismatch".into());
        }
        let p = &self.parameters;
        let f = p.field();
        let mut packed = Vec::with_capacity(self.layout.packed_words);
        for chunk in logical.chunks(p.degree()) {
            let mut word = f.zero();
            for (beta, x) in p.basis().iter().zip(chunk) {
                if p.degree() > 1 {
                    p.extension().extract_base(f, x)?;
                }
                f.add(&mut word, &f.mulf(beta, x));
            }
            packed.push(word);
        }
        Ok(PreparedInputs { logical, packed })
    }
    #[allow(clippy::too_many_arguments)]
    pub fn commit<const W: usize, D: EvaluationDomain<W, F>, R: RandomEngine>(
        self,
        inputs: PreparedInputs<F::E>,
        suffix: Vec<F::E>,
        param: PolygeroParam,
        id: &[u8; 32],
        t: &mut Transcript,
        rng: &mut R,
        domain: &D,
    ) -> Result<CommitmentState<W, F, X>, String>
    where
        F: ZkField<W>,
    {
        let f = self.parameters.field();
        let masks = PackingMasks::sample(&self.parameters, || rng.elt_field(f));
        // Only a nontrivial adapter needs words again. The identity adapter's input
        // equation authenticates directly, with no retained second witness vector.
        let words = if self.layout.degree > 1 {
            inputs.packed.clone()
        } else {
            Vec::new()
        };
        let mut witness = inputs.packed;
        witness.extend_from_slice(masks.cells());
        witness.extend_from_slice(&suffix);
        self.bind(t, id);
        let (polygero, commitment) =
            PolygeroProver::commit(witness, param, t, domain, rng, f).map_err(|e| e.to_string())?;
        Ok(CommitmentState {
            backend: self,
            private: inputs.logical,
            commitment,
            words,
            suffix,
            masks,
            polygero,
        })
    }
}
impl<const W: usize, F: ZkField<W>, X: PackingExtension<Ambient = F>> CommitmentState<W, F, X> {
    pub fn prove<D: EvaluationDomain<W, F>>(
        self,
        statement: CommitmentStatement<F::E>,
        id: &[u8; 32],
        t: &mut Transcript,
        domain: &D,
    ) -> Result<(PackingProof<F::E>, PolygeroProof<F::E>), String> {
        let (packing, rows) = generic::prove_packed(
            &self.backend.parameters,
            &statement.claim,
            &self.words,
            &self.suffix,
            self.masks,
            id,
            t,
        )?;
        drop(self.words);
        drop(self.suffix);
        drop(self.private);
        let binding = super::super::transcript::statement_digest(t);
        let (a, b) = self.backend.authenticate::<W>(statement, &rows)?;
        drop(rows);
        let proof = self
            .polygero
            .prove(&b, t, &a, &binding, domain, self.backend.parameters.field())
            .map_err(|e| e.to_string())?;
        Ok((packing, proof))
    }
}
#[cfg(test)]
#[path = "../tests/commitment.rs"]
mod tests;
