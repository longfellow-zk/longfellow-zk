// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The exponent-tree adapter: the opening protocol of foreign storage.
//!
//! It proves modular linear claims `sum_i c_i * value(group_i) = target (mod r)`
//! whose values are bit groups in the binary commitment. Each claim becomes
//! product trees over GF(2^128)^*: one leaf `1 + b*(g^A - 1)` per committed bit
//! and one leaf per quotient bit, selected by a masked word. The tree root must
//! equal the target power, which is folded into leaf 0 so that the fixed
//! fragment only checks `product = 1`.
//!
//! The fragment is fixed: a pure product tree over virtual inputs. Every
//! challenge-dependent value lives in the per-proof virtual input definitions.
//! The modulus-specific encoder (`p256`, wrapping mode) only computes leaf
//! coefficients, targets and honest quotients. `AdapterMode` packages an
//! encoder with its rounds, pads and message for the composition driver.
pub(crate) mod p256;

use super::reserved::ReservedSuffix;
#[cfg(any(test, feature = "prover"))]
use super::reserved::ReservedWitness;
#[cfg(any(test, feature = "prover"))]
use crate::runtime::random::PrivateRandom;
use crate::{
    core::{
        algebra::{AlgebraicField, SerializableField},
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        v2::{
            proto::composed::AdapterMessage,
            transcript::{Bound, Header},
            zk::{storage::ModularClaim, VirtualInput, VirtualInputs},
        },
    },
};

/// Number of trees and leaves per tree; it fixes the fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TreeShape {
    pub(crate) trees: usize,
    pub(crate) leaves: usize,
}
impl TreeShape {
    /// The number of virtual inputs, `trees * leaves`; None if it overflows.
    pub(crate) fn virtual_inputs(&self) -> Option<usize> {
        self.trees.checked_mul(self.leaves)
    }
}

/// One tree leaf `constant + coefficient * input[source]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Leaf {
    pub(crate) source: usize,
    pub(crate) constant: Gf2_128,
    pub(crate) coefficient: Gf2_128,
}
impl Leaf {
    /// A data leaf `1 + b * (power - 1)`, given `power - 1`.
    pub(crate) fn data(source: usize, power_minus_one: Gf2_128, f: &Gf2_128Field) -> Self {
        Self {
            source,
            constant: f.one(),
            coefficient: power_minus_one,
        }
    }
    /// A quotient leaf `power^(m xor o)` for public bit `m` and committed pad
    /// bit `o`: affine in `o` with coefficients chosen by `m`.
    pub(crate) fn quotient(source: usize, power: Gf2_128, m: bool, f: &Gf2_128Field) -> Self {
        Self {
            source,
            constant: if m { power } else { f.one() },
            coefficient: f.subf(&power, &f.one()),
        }
    }
}

/// One tree's leaves and the value their product must equal.
pub(crate) struct TreeInstance {
    pub(crate) leaves: Vec<Leaf>,
    pub(crate) target: Gf2_128,
}

/// Fold each target into its tree's first leaf and emit the virtual inputs in
/// fragment order: tree-major, leaves in order.
pub(crate) fn virtual_inputs(
    shape: TreeShape,
    trees: Vec<TreeInstance>,
    f: &Gf2_128Field,
) -> Result<VirtualInputs<Gf2_128>, String> {
    if trees.len() != shape.trees || trees.iter().any(|t| t.leaves.len() != shape.leaves) {
        return Err("adapter tree shape".into());
    }
    let mut entries = Vec::with_capacity(shape.virtual_inputs().ok_or("adapter tree shape")?);
    for tree in trees {
        if f.is_zero(&tree.target) {
            return Err("adapter target must be nonzero".into());
        }
        let inverse = f.invert(&tree.target);
        for (i, leaf) in tree.leaves.into_iter().enumerate() {
            let (constant, coefficient) = if i == 0 {
                (
                    f.mulf(&leaf.constant, &inverse),
                    f.mulf(&leaf.coefficient, &inverse),
                )
            } else {
                (leaf.constant, leaf.coefficient)
            };
            entries.push(VirtualInput {
                source: leaf.source,
                constant,
                coefficient,
            });
        }
    }
    Ok(VirtualInputs { entries })
}

/// The adapter fragment: for each tree, the product of its `leaves` virtual
/// inputs must equal one. All coefficients are the constant 1. It is protocol
/// setup, generated at run time from the tree shape; it is not stored in the
/// mdoc archive, which holds only the signature and hash circuits.
///
/// The fragment shares the binary participant's public prefix and input array;
/// its virtual inputs start at `virtual_start`, after the reserved suffix.
pub(crate) fn fragment(
    npublic: usize,
    virtual_start: usize,
    shape: TreeShape,
) -> Result<Circuit<Gf2_128Field>, String> {
    let TreeShape { trees, leaves } = shape;
    if trees == 0 || leaves < 2 || virtual_start < npublic {
        return Err("adapter fragment shape".into());
    }
    let ninput = shape
        .virtual_inputs()
        .and_then(|n| n.checked_add(virtual_start))
        .filter(|&n| n <= u32::MAX as usize)
        .ok_or("adapter fragment width")?;
    let f = Gf2_128Field::new();
    // Layers from the inputs toward the outputs; reversed at the end.
    let mut layers = Vec::new();
    let mut count = leaves;
    let (mut base, mut width) = (virtual_start, ninput);
    while count > 2 {
        let next = count.div_ceil(2);
        let mut quadratic = Vec::new();
        let mut linear = Vec::new();
        for t in 0..trees {
            let (src, dst) = (base + t * count, t * next);
            for i in 0..next {
                let (g, l) = ((dst + i) as u32, (src + 2 * i) as u32);
                if 2 * i + 1 < count {
                    quadratic.push(Quadratic {
                        g,
                        l,
                        r: l + 1,
                        k: 0,
                    });
                } else {
                    linear.push(Linear { g, l, k: 0 });
                }
            }
        }
        layers.push(Layer::new(
            width,
            Stream::<Quadratic>::from_terms(quadratic),
            Stream::<Linear>::from_terms(linear),
            Stream::default(),
        ));
        (base, width, count) = (0, trees * next, next);
    }
    // Output t is l*r + 1, which must vanish: the tree product equals one.
    layers.push(Layer::new(
        width,
        Stream::<Quadratic>::from_terms((0..trees).map(|t| {
            let l = (base + 2 * t) as u32;
            Quadratic {
                g: t as u32,
                l,
                r: l + 1,
                k: 0,
            }
        })),
        Stream::default(),
        Stream::<Constant>::from_terms((0..trees).map(|t| Constant { g: t as u32, k: 0 })),
    ));
    layers.reverse();
    let raw = RawCircuitBuilder {
        ninput,
        npublic_input: npublic,
        noutput: trees,
        logv: crate::util::ceil_log2(trees),
        constants: vec![f.one()],
        layers,
    }
    .build();
    Ok(Circuit::from_raw(&f, raw))
}

/// One way of discharging a split's modular claim over foreign bit groups:
/// the rounds after the claim is fixed, the message they publish, and the
/// fixed fragment whose virtual leaves the binary host proves.
///
/// Implementations are trusted protocol code. Matching these types does not
/// make a mode sound or hiding: each mode must show that its fragment accepts
/// only true claims (up to its stated error), that its message reveals nothing
/// beyond the claim given its pads, and that `prove` and `verify` absorb the
/// same transcript data. Its virtual leaves must depend only on the claim, the
/// mode's own challenges and its published message, all fixed before the host
/// sumcheck begins.
pub(crate) trait AdapterMode<F: SerializableField>: Sized {
    /// Bits of the split mask R in the binary witness.
    const MASK_BITS: usize;
    /// The widest foreign value group the mode accepts (foreign I6). The
    /// prover computes the mode's message from each value's canonical
    /// representative, so a group must be too narrow to hold an integer at
    /// or above the modulus: then its bits are the canonical value whenever
    /// they equal the value modulo the prime. R's group is exempt, because
    /// the prover writes R's canonical bits itself.
    const MAX_VALUE_BITS: usize;
    /// Committed one-time pads, built only by the prover.
    type Pads;
    /// The published message.
    type Message: AdapterMessage;
    /// A mode for a claim whose term widths are `widths`, in term order. It
    /// allocates its pads in `suffix`, after R; its fragment reads the host's
    /// `npublic` public inputs and the virtual inputs after the suffix.
    fn new(widths: Vec<usize>, npublic: usize, suffix: &mut ReservedSuffix)
        -> Result<Self, String>;
    fn fragment(&self) -> &Circuit<Gf2_128Field>;
    fn virtual_inputs(&self) -> usize;
    /// Write the mode's `AdapterLayout` statement message.
    fn write_layout(&self, h: &mut Header<'_>);
    #[cfg(any(test, feature = "prover"))]
    fn sample_pads(&self, rng: &mut impl PrivateRandom) -> Self::Pads;
    #[cfg(any(test, feature = "prover"))]
    fn write_pads(
        &self,
        pads: &Self::Pads,
        reserved: &mut ReservedWitness<'_>,
    ) -> Result<(), String>;
    /// Prover rounds, which draw the mode's input challenge on entry, before
    /// they send (transcript I8): `values` are the claim's term values, in term order.
    /// They consume the proof's fresh `pads`, so a pad masks one message.
    #[cfg(any(test, feature = "prover"))]
    fn prove(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<F::E>,
        values: &[F::E],
        pads: Self::Pads,
        f: &F,
        gf2: &Gf2_128Field,
    ) -> Result<(Self::Message, VirtualInputs<Gf2_128>), String>;
    /// Verifier rounds from the published message, which draw the same input
    /// challenge on entry.
    #[cfg(any(test, feature = "verifier"))]
    fn verify(
        t: &mut Bound<'_, Self>,
        claim: &ModularClaim<F::E>,
        message: &Self::Message,
        f: &F,
        gf2: &Gf2_128Field,
    ) -> Result<VirtualInputs<Gf2_128>, String>;
}
