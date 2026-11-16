// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The Polygero error type and its precondition helper.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolygeroError(pub(super) String);
impl std::fmt::Display for PolygeroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for PolygeroError {}
impl From<std::io::Error> for PolygeroError {
    fn from(error: std::io::Error) -> Self {
        Self(error.to_string())
    }
}
pub(super) fn ensure(condition: bool, message: &str) -> Result<(), PolygeroError> {
    if condition {
        Ok(())
    } else {
        Err(PolygeroError(message.into()))
    }
}
