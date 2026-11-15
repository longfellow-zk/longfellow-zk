// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! An owned Boolean advice contract. Packed words represent independent lanes;
//! there is no field arithmetic or compiler/runtime state in this representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdviceNode {
    Input(usize),
    Xor(Vec<usize>, bool),
    And(usize, usize),
}
#[derive(Clone, Debug)]
pub struct BooleanAdvice {
    inputs: usize,
    nodes: Vec<AdviceNode>,
    outputs: Vec<usize>,
}
impl BooleanAdvice {
    pub fn new(inputs: usize, nodes: Vec<AdviceNode>, outputs: Vec<usize>) -> Result<Self, String> {
        for (i, node) in nodes.iter().enumerate() {
            let valid = match node {
                AdviceNode::Input(j) => *j < inputs,
                AdviceNode::And(a, b) => *a < i && *b < i,
                AdviceNode::Xor(xs, _) => xs.iter().all(|&j| j < i),
            };
            if !valid {
                return Err("non-topological Boolean advice".into());
            }
        }
        if outputs.iter().any(|&j| j >= nodes.len()) {
            return Err("Boolean advice output index".into());
        }
        Ok(Self {
            inputs,
            nodes,
            outputs,
        })
    }
    pub fn inputs(&self) -> usize {
        self.inputs
    }
    pub fn additional_words(&self) -> usize {
        self.outputs.len()
    }
    pub fn evaluate(&self, original: &[u128]) -> Result<Vec<u128>, String> {
        if original.len() != self.inputs {
            return Err("Boolean advice input length".into());
        }
        let mut values = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            values.push(match node {
                AdviceNode::Input(i) => original[*i],
                AdviceNode::And(a, b) => values[*a] & values[*b],
                AdviceNode::Xor(xs, c) => xs
                    .iter()
                    .fold(if *c { u128::MAX } else { 0 }, |x, &i| x ^ values[i]),
            });
        }
        let mut out = original.to_vec();
        out.extend(self.outputs.iter().map(|&i| values[i]));
        Ok(out)
    }
}

#[cfg(test)]
mod tests;
