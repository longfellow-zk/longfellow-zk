// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// The dense two-phase prover eliminates hand 0 before hand 1.
pub const HAND_ORDER: [usize; 2] = [0, 1];

/// Sumcheck challenge schedule. Hand-major accepts any circuit traversal;
/// round-major proving requires the circuit to already be in Morton order.
/// Select this from the agreed protocol/specification, never by inspecting a
/// circuit's term order or by trying to verify with both schedules.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SumcheckOrder {
    /// Complete h0 before h1; enables the dense two-pass prover.
    #[default]
    HandMajor,
    /// Legacy/C++ schedule: h0 bit 0, h1 bit 0, h0 bit 1, h1 bit 1, ...
    /// Requires Morton-ordered circuit terms; the prover does not sort them.
    RoundMajor,
}

impl SumcheckOrder {
    /// `(hand, bit)` in transcript order, low bits first within each hand.
    pub fn rounds(self, logw: usize) -> impl Iterator<Item = (usize, usize)> {
        (0..2 * logw).map(move |i| match self {
            Self::HandMajor => (i / logw, i % logw),
            Self::RoundMajor => (i % 2, i / 2),
        })
    }
}

/// `(hand, bit)` in transcript order: all h0 bits, then all h1 bits,
/// least significant first within each hand. Dense hand polynomials decouple
/// this order from circuit term traversal; there are no sparse adjacency constraints.
///
/// Proof arrays and padding witnesses are still indexed by hand and bit; their
/// serialization/allocation order is independent of this transcript order.
#[inline]
pub fn round_order(logw: usize) -> impl Iterator<Item = (usize, usize)> {
    SumcheckOrder::HandMajor.rounds(logw)
}

#[cfg(test)]
mod tests {
    use super::{round_order, SumcheckOrder};

    #[test]
    fn legacy_rounds_interleave_hands_and_allow_zero_width() {
        assert_eq!(
            SumcheckOrder::RoundMajor.rounds(3).collect::<Vec<_>>(),
            [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2), (1, 2)]
        );
        for order in [SumcheckOrder::HandMajor, SumcheckOrder::RoundMajor] {
            assert_eq!(order.rounds(0).count(), 0);
            assert_eq!(order.rounds(1).collect::<Vec<_>>(), [(0, 0), (1, 0)]);
        }
    }

    #[test]
    fn dense_rounds_complete_hand_zero_before_hand_one() {
        assert_eq!(
            round_order(3).collect::<Vec<_>>(),
            [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
        );
        assert_eq!(round_order(1).collect::<Vec<_>>(), [(0, 0), (1, 0)]);
        assert_eq!(round_order(0).count(), 0);
    }
}
