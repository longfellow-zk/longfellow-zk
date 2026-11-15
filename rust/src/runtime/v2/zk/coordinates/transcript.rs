// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Setup messages for coordinate storage. The frontend writes its circuit ID.
use super::affine::AffineEncoding;
use crate::runtime::v2::{
    proto::tags::Tag,
    transcript::{Encoder, Header, Message, SetupMessage},
};

struct Layout<'a>(&'a [usize]);
impl Message for Layout<'_> {
    const TAG: Tag = Tag::CoordinateLayout;
    fn encode(&self, e: &mut Encoder<'_>) {
        e.nats(&self.0.iter().map(|&x| x as u64).collect::<Vec<_>>());
    }
}
impl SetupMessage for Layout<'_> {}

pub(super) fn write_layout(h: &mut Header<'_>, words: &[usize]) {
    h.send(&Layout(words));
}

struct Affine<'a>(&'a [AffineEncoding]);
impl Message for Affine<'_> {
    const TAG: Tag = Tag::CoordinateAffine;
    fn encode(&self, e: &mut Encoder<'_>) {
        let mut words = Vec::with_capacity(1 + 2 * self.0.len());
        words.push(self.0.len() as u64);
        for encoding in self.0 {
            words.extend([encoding.scale as u64, encoding.offset as u64]);
        }
        e.nats(&words);
    }
}
impl SetupMessage for Affine<'_> {}

/// Signed affine parameters use fixed-width two's-complement integers.
pub(super) fn write_affine(h: &mut Header<'_>, encodings: &[AffineEncoding]) {
    h.send(&Affine(encodings));
}
