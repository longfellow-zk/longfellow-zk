// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! V2 application statement framing shared by the mdoc proof roles.
use crate::runtime::v2::transcript::{Transcript, TranscriptRef};

pub(super) fn new(context: &[u8], combined_hash: &[u8; 32]) -> Transcript {
    let mut transcript = Transcript::new(context);
    transcript.bind(|w| {
        w.write_bytes(b"mdoc/adapter/statement/v1");
        w.write_bytes(combined_hash);
    });
    transcript
}

/// Fix the public presentation bits before receiving the shared commitment.
pub(super) fn bind_public_inputs(transcript: &mut TranscriptRef<'_>, public: &[bool]) {
    transcript.bind(|w| w.write_bytes(&public.iter().map(|&b| u8::from(b)).collect::<Vec<_>>()));
}
