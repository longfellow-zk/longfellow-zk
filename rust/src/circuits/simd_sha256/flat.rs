// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
//! Single QUAD with shared, packed intermediate witnesses. Linear aliases are
//! substituted away; only cuts needed to keep the residuals quadratic remain.
use std::collections::{BTreeMap, BTreeSet};

use super::{circuit::compile_base, INPUT_BITS};
use crate::{
    compile::algebra::gf2_128::Gf2_128Field as F,
    core::proto::v2::{
        Circuit, Constant, Layer, Linear, Quadratic, RawCircuit, RawCircuitBuilder, Stream,
    },
};

#[derive(Clone, Copy, Debug)]
pub enum Policy {
    /// Cut nested products; expand every affine AND operand.
    Products,
    /// Cut complex AND operands, avoiding Cartesian product expansion.
    Operands,
    /// Cut an affine operand when its expanded size exceeds this threshold.
    Bounded(usize),
}

use crate::core::proto::advice::{AdviceNode as Node, BooleanAdvice};
struct Dag {
    nodes: Vec<Node>,
    index: BTreeMap<Node, usize>,
}
/// An owned, topologically ordered slice of the DAG needed for specific advice.
struct AdviceRecipe;
impl AdviceRecipe {
    fn build(dag: &Dag, outputs: &[usize]) -> BooleanAdvice {
        let mut needed = vec![false; dag.nodes.len()];
        let mut stack = outputs.to_vec();
        while let Some(i) = stack.pop() {
            if needed[i] {
                continue;
            }
            needed[i] = true;
            match &dag.nodes[i] {
                Node::Input(_) => {}
                Node::Xor(xs, _) => stack.extend_from_slice(xs),
                Node::And(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
            }
        }
        let mut map = vec![usize::MAX; dag.nodes.len()];
        let mut nodes = Vec::new();
        for (i, node) in dag.nodes.iter().enumerate() {
            if needed[i] {
                let remapped = match node {
                    Node::Input(x) => Node::Input(*x),
                    Node::And(a, b) => Node::And(map[*a], map[*b]),
                    Node::Xor(xs, c) => Node::Xor(xs.iter().map(|&j| map[j]).collect(), *c),
                };
                map[i] = nodes.len();
                nodes.push(remapped);
            }
        }
        BooleanAdvice::new(INPUT_BITS, nodes, outputs.iter().map(|&i| map[i]).collect())
            .expect("compiler advice is topological")
    }
}
impl Dag {
    fn new() -> Self {
        let mut out = Self {
            nodes: vec![],
            index: BTreeMap::new(),
        };
        out.intern(Node::Xor(vec![], false));
        out.intern(Node::Xor(vec![], true));
        out
    }
    fn intern(&mut self, node: Node) -> usize {
        if let Some(&id) = self.index.get(&node) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push(node.clone());
        self.index.insert(node, id);
        id
    }
    fn xor(&mut self, terms: Vec<usize>) -> usize {
        let mut list = Vec::new();
        let mut constant = false;
        for id in terms {
            if let Node::Xor(xs, c) = &self.nodes[id] {
                list.extend_from_slice(xs);
                constant ^= c;
            } else {
                list.push(id);
            }
        }
        parity(&mut list);
        if list.len() == 1 && !constant {
            return list[0];
        }
        self.intern(Node::Xor(list, constant))
    }
    fn and(&mut self, a: usize, b: usize) -> usize {
        if a == 0 || b == 0 {
            return 0;
        }
        if a == b || b == 1 {
            return a;
        }
        if a == 1 {
            return b;
        }
        self.intern(Node::And(a.min(b), a.max(b)))
    }
    fn from_circuit(c: &Circuit<F>) -> (Self, Vec<usize>) {
        let mut dag = Self::new();
        let mut input: Vec<_> = (0..c.raw.ninput)
            .map(|i| dag.intern(Node::Input(i)))
            .collect();
        let mut roots = Vec::new();
        for (i, l) in c.raw.layers.iter().enumerate().rev() {
            let n = if i == 0 {
                c.raw.noutput
            } else {
                c.raw.layers[i - 1].nw
            };
            let mut out = vec![Vec::new(); n];
            l.quadratic.for_each(|v| {
                let a = dag.and(input[v.l as usize], input[v.r as usize]);
                if c.raw.constants[v.k as usize].word() == 0 {
                    roots.push(a);
                } else {
                    out[v.g as usize].push(a);
                }
            });
            l.linear.for_each(|v| {
                let a = input[v.l as usize];
                if c.raw.constants[v.k as usize].word() == 0 {
                    roots.push(a);
                } else {
                    out[v.g as usize].push(a);
                }
            });
            l.constant.for_each(|v| {
                if c.raw.constants[v.k as usize].word() != 0 {
                    out[v.g as usize].push(1);
                }
            });
            input = out.into_iter().map(|xs| dag.xor(xs)).collect();
        }
        roots.extend(input);
        let mut seen = BTreeSet::new();
        roots.retain(|&id| id != 0 && seen.insert(id));
        (dag, roots)
    }
}
fn parity<T: Ord + Copy>(xs: &mut Vec<T>) {
    xs.sort_unstable();
    let mut write = 0;
    let mut i = 0;
    while i < xs.len() {
        let x = xs[i];
        let mut end = i + 1;
        while end < xs.len() && xs[end] == x {
            end += 1;
        }
        if (end - i) % 2 != 0 {
            xs[write] = x;
            write += 1;
        }
        i = end;
    }
    xs.truncate(write);
}
struct Cuts<'a> {
    dag: &'a Dag,
    policy: Policy,
    nodes: BTreeSet<usize>,
    quadratic_seen: BTreeSet<usize>,
    affine_seen: BTreeSet<usize>,
}
impl Cuts<'_> {
    fn cut(&mut self, id: usize) {
        if self.nodes.insert(id) {
            self.quadratic(id);
        }
    }
    fn affine(&mut self, id: usize) {
        if self.nodes.contains(&id) || !self.affine_seen.insert(id) {
            return;
        }
        match &self.dag.nodes[id] {
            Node::Input(_) => {}
            Node::And(..) => self.cut(id),
            Node::Xor(xs, _) => {
                let cut = match self.policy {
                    Policy::Products => false,
                    Policy::Operands => !xs.is_empty(),
                    Policy::Bounded(n) => xs.len() > n,
                };
                if cut {
                    self.cut(id);
                } else {
                    for &x in xs {
                        self.affine(x);
                    }
                }
            }
        }
    }
    fn quadratic(&mut self, id: usize) {
        if !self.quadratic_seen.insert(id) {
            return;
        }
        match &self.dag.nodes[id] {
            Node::Input(_) => {}
            Node::Xor(xs, _) => {
                for &x in xs {
                    if !self.nodes.contains(&x) {
                        self.quadratic(x);
                    }
                }
            }
            Node::And(a, b) => {
                self.affine(*a);
                self.affine(*b);
            }
        }
    }
}
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Affine {
    pub vars: Vec<usize>,
    pub constant: bool,
}
struct Forms {
    real_inputs: usize,
    forms: Vec<Affine>,
    index: BTreeMap<Affine, usize>,
}
impl Forms {
    fn get(&mut self, form: Affine) -> usize {
        if form.vars.len() == 1 && !form.constant {
            return form.vars[0];
        }
        if let Some(&i) = self.index.get(&form) {
            return i;
        }
        let i = self.real_inputs + self.forms.len();
        self.index.insert(form.clone(), i);
        self.forms.push(form);
        i
    }
}
#[derive(Default)]
struct Polynomial {
    linear: Vec<usize>,
    quadratic: Vec<(usize, usize)>,
    constant: bool,
}
struct Lowering<'a> {
    dag: &'a Dag,
    variables: &'a BTreeMap<usize, usize>,
    affine: BTreeMap<usize, Affine>,
    forms: Option<Forms>,
}
impl Lowering<'_> {
    fn affine(&mut self, id: usize) -> Affine {
        if let Some(x) = self.affine.get(&id) {
            return x.clone();
        }
        let out = if let Some(&i) = self.variables.get(&id) {
            Affine {
                vars: vec![i],
                constant: false,
            }
        } else {
            match &self.dag.nodes[id] {
                Node::Input(i) => Affine {
                    vars: vec![*i],
                    constant: false,
                },
                Node::Xor(xs, c) => {
                    let mut out = Affine {
                        vars: vec![],
                        constant: *c,
                    };
                    for &x in xs {
                        let a = self.affine(x);
                        out.vars.extend(a.vars);
                        out.constant ^= a.constant;
                    }
                    parity(&mut out.vars);
                    out
                }
                Node::And(..) => panic!("nonlinear expression without a witness cut"),
            }
        };
        self.affine.insert(id, out.clone());
        out
    }
    fn append(&mut self, id: usize, root: bool, out: &mut Polynomial) {
        if !root {
            if let Some(&i) = self.variables.get(&id) {
                out.linear.push(i);
                return;
            }
        }
        match &self.dag.nodes[id] {
            Node::Input(i) => out.linear.push(*i),
            Node::Xor(xs, c) => {
                out.constant ^= c;
                for &x in xs {
                    self.append(x, false, out);
                }
            }
            Node::And(left, right) => {
                let a = self.affine(*left);
                let b = self.affine(*right);
                if let Some(forms) = &mut self.forms {
                    let x = forms.get(a);
                    let y = forms.get(b);
                    if x == y {
                        out.linear.push(x);
                    } else {
                        out.quadratic.push((x.min(y), x.max(y)));
                    }
                    return;
                }
                out.constant ^= a.constant && b.constant;
                if a.constant {
                    out.linear.extend_from_slice(&b.vars);
                }
                if b.constant {
                    out.linear.extend_from_slice(&a.vars);
                }
                for &x in &a.vars {
                    for &y in &b.vars {
                        // All application inputs, including the advice, are bits
                        // represented as bit planes: x^2 = x.
                        if x == y {
                            out.linear.push(x);
                        } else {
                            out.quadratic.push((x.min(y), x.max(y)));
                        }
                    }
                }
            }
        }
    }
}

pub struct FlatCircuit {
    pub circuit: Circuit<F>,
    dag: Dag,
    cuts: Vec<usize>,
    roots: Vec<usize>,
    recipe: BooleanAdvice,
}
impl FlatCircuit {
    pub fn additional_bits_per_lane(&self) -> usize {
        self.cuts.len()
    }
    /// Compute the extra witness bits once per shared expression, packed across
    /// all 128 lanes. The original SHA witness remains the unchanged prefix.
    pub fn advice(&self) -> &BooleanAdvice {
        &self.recipe
    }
    /// Factor the very same quadratic residuals into products of affine forms.
    /// The extra coordinates here are computed XORs, not witness inputs. Their
    /// coefficients are substituted back before authenticating the opening.
    pub fn factored(&self) -> (Circuit<F>, Vec<Affine>) {
        let variables: BTreeMap<_, _> = self
            .cuts
            .iter()
            .enumerate()
            .map(|(i, &id)| (id, INPUT_BITS + i))
            .collect();
        let real = self.circuit.raw.ninput;
        let mut lowering = Lowering {
            dag: &self.dag,
            variables: &variables,
            affine: BTreeMap::new(),
            forms: Some(Forms {
                real_inputs: real,
                forms: vec![],
                index: BTreeMap::new(),
            }),
        };
        let raw = lower(&mut lowering, &self.roots, &self.cuts, &variables, real);
        let forms = lowering.forms.unwrap().forms;
        let circuit = Circuit::from_raw(&F::new(), raw);
        (circuit, forms)
    }
}
pub fn compile(policy: Policy) -> Result<FlatCircuit, String> {
    let base = compile_base()?;
    let (dag, roots) = Dag::from_circuit(&base);
    let mut selection = Cuts {
        dag: &dag,
        policy,
        nodes: BTreeSet::new(),
        quadratic_seen: BTreeSet::new(),
        affine_seen: BTreeSet::new(),
    };
    for &id in &roots {
        selection.quadratic(id);
    }
    let cuts: Vec<_> = selection.nodes.into_iter().collect();
    let variables: BTreeMap<_, _> = cuts
        .iter()
        .enumerate()
        .map(|(i, &id)| (id, INPUT_BITS + i))
        .collect();
    let mut lowering = Lowering {
        dag: &dag,
        variables: &variables,
        affine: BTreeMap::new(),
        forms: None,
    };
    let raw = lower(
        &mut lowering,
        &roots,
        &cuts,
        &variables,
        INPUT_BITS + cuts.len(),
    );
    let circuit = Circuit::from_raw(&F::new(), raw);
    assert_eq!(circuit.raw.layers.len(), 1);
    let recipe = AdviceRecipe::build(&dag, &cuts);
    Ok(FlatCircuit {
        circuit,
        dag,
        cuts,
        roots,
        recipe,
    })
}
fn lower(
    lowering: &mut Lowering<'_>,
    roots: &[usize],
    cuts: &[usize],
    variables: &BTreeMap<usize, usize>,
    real_inputs: usize,
) -> RawCircuit<F> {
    let mut q = Vec::new();
    let mut l = Vec::new();
    let mut k = Vec::new();
    let mut noutput = 0;
    for (&id, witness) in roots
        .iter()
        .map(|id| (id, None))
        .chain(cuts.iter().map(|id| (id, Some(variables[id]))))
    {
        let mut p = Polynomial::default();
        lowering.append(id, witness.is_some(), &mut p);
        if let Some(i) = witness {
            p.linear.push(i);
        }
        parity(&mut p.linear);
        parity(&mut p.quadratic);
        if p.linear.is_empty() && p.quadratic.is_empty() && !p.constant {
            continue;
        }
        let g = noutput as u32;
        noutput += 1;
        q.extend(p.quadratic.into_iter().map(|(a, b)| Quadratic {
            g,
            l: a as u32,
            r: b as u32,
            k: 1,
        }));
        l.extend(p.linear.into_iter().map(|a| Linear {
            g,
            l: a as u32,
            k: 1,
        }));
        if p.constant {
            k.push(Constant { g, k: 1 });
        }
    }
    let ninput = real_inputs + lowering.forms.as_ref().map_or(0, |x| x.forms.len());
    RawCircuitBuilder {
        ninput,
        npublic_input: 0,
        noutput,
        logv: noutput.next_power_of_two().trailing_zeros() as usize,
        constants: vec![F::new().zero(), F::new().one()],
        layers: vec![Layer::new(
            ninput,
            compact_stream(q, |t, p| Quadratic {
                g: t.g.wrapping_sub(p.g),
                l: t.l.wrapping_sub(p.l),
                r: t.r.wrapping_sub(p.r),
                k: t.k,
            }),
            compact_stream(l, |t, p| Linear {
                g: t.g.wrapping_sub(p.g),
                l: t.l.wrapping_sub(p.l),
                k: t.k,
            }),
            compact_stream(k, |t, p| Constant {
                g: t.g.wrapping_sub(p.g),
                k: t.k,
            }),
        )],
    }
    .build()
}

trait Record: Copy + Default {
    fn key(&self) -> [u32; 4];
}
impl Record for Quadratic {
    fn key(&self) -> [u32; 4] {
        [self.g, self.l, self.r, self.k]
    }
}
impl Record for Linear {
    fn key(&self) -> [u32; 4] {
        [self.g, self.l, self.k, 0]
    }
}
impl Record for Constant {
    fn key(&self) -> [u32; 4] {
        [self.g, self.k, 0, 0]
    }
}
/// Offline dictionary construction by sorting. Runtime traversal then reads
/// compact arrays; neither construction nor traversal needs a hash table.
fn compact_stream<T: Record>(terms: Vec<T>, delta: impl Fn(T, T) -> T) -> Stream<T> {
    if terms.is_empty() {
        return Stream::default();
    }
    let n = terms.len();
    u32::try_from(n).expect("SHA stream size");
    let mut previous = T::default();
    let deltas: Vec<_> = terms
        .into_iter()
        .map(|term| {
            let d = delta(term, previous);
            previous = term;
            d
        })
        .collect();
    let mut order: Vec<_> = (0..n).collect();
    order.sort_unstable_by_key(|&i| deltas[i].key());
    let mut dictionary = Vec::<T>::new();
    let mut run = vec![0u32; n];
    for i in order {
        if dictionary
            .last()
            .is_none_or(|last| last.key() != deltas[i].key())
        {
            dictionary.push(deltas[i]);
        }
        run[i] = (dictionary.len() - 1) as u32;
    }
    Stream {
        deltas: dictionary,
        segments: vec![run].into(),
        tokens: vec![0],
    }
}

use crate::core::algebra::AlgebraicField;
