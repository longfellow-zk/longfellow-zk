// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

impl BitViews {
    pub(crate) fn expand(&self, words: &[E]) -> Vec<E> {
        self.forms
            .iter()
            .map(|form| {
                E::from(form.terms.iter().fold(form.constant, |word, t| {
                    word ^ self.maps[t.map].apply(words[t.word].to_u128())
                }))
            })
            .collect()
    }
}
