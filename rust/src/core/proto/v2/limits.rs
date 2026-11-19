// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Global v2 reader limits. The wire ceiling is just over three times the
//! largest current mdoc circuit (2,648,473 wires including its inputs/outputs).
//! Segment/token metadata includes directory offsets and decoder summaries.

pub const MAX_LAYERS: usize = 128;
pub const MAX_TOTAL_WIRES: usize = 1 << 23;
pub const MAX_METADATA_BYTES: usize = 10 * 1024 * 1024;
// Also bound stored coefficients/deltas/indices: unused dictionary data must
// not escape the same global ceiling that bounds expanded evaluation work.
pub const MAX_TOTAL_TERMS: usize = 1 << 24;
// Container/file I/O has one coarse byte ceiling, shared by compressed and
// uncompressed artifacts. No individual field, layer or stream has its own cap.
pub const MAX_ARCHIVE_BYTES: usize = 4 * MAX_TOTAL_TERMS;
pub const MAX_ARCHIVE_ENTRIES: usize = 3;
