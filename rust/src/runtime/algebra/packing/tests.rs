// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{AmbientElement, BaseElement, PackingExtension, PackingParameters};

impl<X: PackingExtension> PackingParameters<X> {
    /// Every field, in declaration order: the field, the extension, the
    /// basis, the trace-dual basis and the coordinate inverse. The pattern is
    /// exhaustive, so a new field does not compile until the statement tests
    /// cover it.
    pub(crate) fn fields_for_test(
        &self,
    ) -> (
        &X::Ambient,
        &X,
        &[AmbientElement<X>],
        &[AmbientElement<X>],
        Option<&[Vec<BaseElement<X>>]>,
    ) {
        let Self {
            field,
            extension,
            basis,
            dual,
            inverse,
        } = self;
        (field, extension, basis, dual, inverse.as_deref())
    }
}
