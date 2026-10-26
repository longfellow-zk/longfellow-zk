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

//! A field-independent Boolean DAG used only to prepare extra witness bits.
use super::PackedBits;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BitOp {
    Input(usize),
    Constant(bool),
    Xor(usize, usize),
    And(usize, usize),
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BitRecipe {
    pub nodes: Vec<BitOp>,
    pub outputs: Vec<usize>,
}
impl BitRecipe {
    pub fn validate(&self, inputs: usize) -> Result<(), String> {
        for (i, op) in self.nodes.iter().enumerate() {
            let valid = match *op {
                BitOp::Input(n) => n < inputs,
                BitOp::Constant(_) => true,
                BitOp::Xor(a, b) | BitOp::And(a, b) => a < i && b < i,
            };
            if !valid {
                return Err("invalid Boolean witness recipe".into());
            }
        }
        if self.outputs.iter().any(|&i| i >= self.nodes.len()) {
            return Err("invalid recipe output".into());
        }
        Ok(())
    }
    pub fn evaluate(&self, inputs: &PackedBits) -> Result<PackedBits, String> {
        self.validate(inputs.len())?;
        let mut nodes = PackedBits::with_capacity(self.nodes.len());
        for op in &self.nodes {
            let bit = match *op {
                BitOp::Input(i) => inputs.get(i),
                BitOp::Constant(b) => b,
                BitOp::Xor(a, b) => nodes.get(a) ^ nodes.get(b),
                BitOp::And(a, b) => nodes.get(a) & nodes.get(b),
            };
            nodes.push(bit);
        }
        Ok(self.outputs.iter().map(|&i| nodes.get(i)).collect())
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut b = Vec::new();
        b.extend_from_slice(&(self.nodes.len() as u64).to_le_bytes());
        for op in &self.nodes {
            match *op {
                BitOp::Input(i) => {
                    b.push(0);
                    b.extend_from_slice(&(i as u64).to_le_bytes())
                }
                BitOp::Constant(v) => {
                    b.push(1);
                    b.push(u8::from(v))
                }
                BitOp::Xor(a, c) | BitOp::And(a, c) => {
                    b.push(if matches!(op, BitOp::Xor(..)) { 2 } else { 3 });
                    b.extend_from_slice(&(a as u64).to_le_bytes());
                    b.extend_from_slice(&(c as u64).to_le_bytes())
                }
            }
        }
        b.extend_from_slice(&(self.outputs.len() as u64).to_le_bytes());
        for &i in &self.outputs {
            b.extend_from_slice(&(i as u64).to_le_bytes())
        }
        b
    }
    pub fn from_bytes(mut b: &[u8]) -> Result<Self, String> {
        fn number(b: &mut &[u8]) -> Result<usize, String> {
            let c = b.get(..8).ok_or("truncated recipe")?;
            let n = usize::try_from(u64::from_le_bytes(c.try_into().unwrap()))
                .map_err(|_| "recipe index overflow")?;
            *b = &b[8..];
            Ok(n)
        }
        fn byte(b: &mut &[u8]) -> Result<u8, String> {
            let n = *b.first().ok_or("truncated recipe")?;
            *b = &b[1..];
            Ok(n)
        }
        let node_count = number(&mut b)?;
        if node_count > b.len() / 2 {
            return Err("truncated recipe nodes".into());
        }
        let mut nodes = Vec::with_capacity(node_count);
        for _ in 0..node_count {
            nodes.push(match byte(&mut b)? {
                0 => BitOp::Input(number(&mut b)?),
                1 => match byte(&mut b)? {
                    0 => BitOp::Constant(false),
                    1 => BitOp::Constant(true),
                    _ => return Err("invalid recipe bit".into()),
                },
                2 => BitOp::Xor(number(&mut b)?, number(&mut b)?),
                3 => BitOp::And(number(&mut b)?, number(&mut b)?),
                _ => return Err("invalid recipe opcode".into()),
            })
        }
        let output_count = number(&mut b)?;
        if output_count != b.len() / 8 || !b.len().is_multiple_of(8) {
            return Err("invalid recipe outputs".into());
        }
        let mut outputs = Vec::with_capacity(output_count);
        for _ in 0..output_count {
            outputs.push(number(&mut b)?)
        }
        Ok(Self { nodes, outputs })
    }
}
