// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! The exponent-tree adapter: the opening protocol of foreign storage.
//!
//! It proves modular linear claims `sum_i c_i * value(group_i) = target (mod r)`
//! whose values are bit groups in the binary commitment. Each claim becomes
//! product trees over GF(2^128)^*: one leaf `1 + b*(g^A - 1)` per committed bit
//! and one leaf per quotient bit, selected by a masked word. The tree root must
//! equal the target power, which is folded into leaf 0 so that the archived
//! fragment only checks `product = 1`.
//!
//! The fragment is fixed: a pure product tree over virtual inputs. Every
//! challenge-dependent value lives in the per-proof virtual input definitions.
//! The modulus-specific encoders (`p256` wrapping, `exact` small-prime) only
//! compute leaf coefficients, targets and honest quotients.
pub(crate) mod integer;
pub mod p256;
mod transcript;

use super::storage::Group;
use crate::{
    core::{
        algebra::AlgebraicField,
        proto::v2::{Circuit, Constant, Layer, Linear, Quadratic, RawCircuitBuilder, Stream},
    },
    runtime::{
        algebra::gf2_128::{Gf2_128, Gf2_128Field},
        v2::zk::{VirtualInput, VirtualInputs},
    },
};

/// A linear claim over foreign-stored values, modulo the claim field's order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModularClaim<E> {
    pub terms: Vec<(Group, E)>,
    pub target: E,
}
impl<E> ModularClaim<E> {
    /// Total committed bits read by the claim.
    pub fn bits(&self) -> usize {
        self.terms.iter().map(|(g, _)| g.width).sum()
    }
}

/// Number of trees and leaves per tree; it fixes the archived fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    pub trees: usize,
    pub leaves: usize,
}
impl TreeShape {
    pub fn virtual_inputs(&self) -> usize {
        self.trees * self.leaves
    }
}

/// One tree leaf `constant + coefficient * input[source]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf {
    pub source: usize,
    pub constant: Gf2_128,
    pub coefficient: Gf2_128,
}
impl Leaf {
    /// A data leaf `1 + b * (power - 1)`, given `power - 1`.
    pub fn data(source: usize, power_minus_one: Gf2_128, f: &Gf2_128Field) -> Self {
        Self {
            source,
            constant: f.one(),
            coefficient: power_minus_one,
        }
    }
    /// A quotient leaf `power^(m xor o)` for public bit `m` and committed pad
    /// bit `o`: affine in `o` with coefficients chosen by `m`.
    pub fn quotient(source: usize, power: Gf2_128, m: bool, f: &Gf2_128Field) -> Self {
        Self {
            source,
            constant: if m { power } else { f.one() },
            coefficient: f.subf(&power, &f.one()),
        }
    }
}

/// One tree's leaves and the value their product must equal.
pub struct TreeInstance {
    pub leaves: Vec<Leaf>,
    pub target: Gf2_128,
}

/// Fold each target into its tree's first leaf and emit the virtual inputs in
/// fragment order: tree-major, leaves in order.
pub fn virtual_inputs(
    shape: TreeShape,
    trees: Vec<TreeInstance>,
    f: &Gf2_128Field,
) -> Result<VirtualInputs<Gf2_128>, String> {
    if trees.len() != shape.trees || trees.iter().any(|t| t.leaves.len() != shape.leaves) {
        return Err("adapter tree shape".into());
    }
    let mut entries = Vec::with_capacity(shape.virtual_inputs());
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

/// The archived adapter fragment: for each tree, the product of its `leaves`
/// virtual inputs must equal one. All coefficients are the constant 1.
///
/// The fragment shares the binary participant's public prefix and input array;
/// its virtual inputs start at `virtual_start`, after the reserved suffix.
pub fn fragment(
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
        .checked_add(virtual_start)
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
        layers.push(Layer::with_assertions(
            width,
            Stream::<Quadratic>::from_terms(quadratic),
            Stream::<Linear>::from_terms(linear),
            Stream::default(),
            |_| false,
        ));
        (base, width, count) = (0, trees * next, next);
    }
    // Output t is l*r + 1, which must vanish: the tree product equals one.
    layers.push(Layer::with_assertions(
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
        |_| false,
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
