// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::runtime::v2::zk::verifier::reduce_values;
/// Check the pure-foreign frontend proof of `t`'s part and reduce its
/// constraints to its unbatched rows.
pub(crate) fn reduce<F: ZkField + PackingField>(
    t: &mut Bound<'_, FrontendPart<'_, F, PureSplit<F>>>,
    proof: &SumcheckProof<F>,
) -> Result<PureClaim<F::E>, String> {
    let constraints = reduce_values(t, proof)?;
    frontend_claim(t.part(), constraints)
}
