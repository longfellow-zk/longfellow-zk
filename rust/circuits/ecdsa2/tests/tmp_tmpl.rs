use circuits_ecdsa2::EcdsaCircuit;
use compile_algebra::{p256::P256Field, secp256r1::Secp256r1};
use compile_compiler::{cert, compile_with_cert, quad::WExpr};
use core_algebra::SerializableField;
use std::collections::HashMap;

/// Canonical shape of the sub-DAG rooted at `n`, to depth `d`: node kinds and constant
/// values, with operands identified by BFS position rather than absolute index.
fn shape<F: compile_algebra::field::CompileField + SerializableField>(
    f: &F,
    nodes: &[WExpr<F>],
    n: usize,
    d: usize,
    out: &mut Vec<u8>,
) {
    if d == 0 {
        out.push(0xFF);
        return;
    }
    match &nodes[n] {
        WExpr::Input { .. } => out.push(0x01),
        WExpr::Assert0(w) => {
            out.push(0x02);
            shape(f, nodes, *w, d - 1, out);
        }
        WExpr::Sum(ts) => {
            out.push(0x03);
            out.extend_from_slice(&(ts.len() as u32).to_le_bytes());
            for (k, w0, w1) in ts {
                out.extend_from_slice(&f.to_bytes(k));
                shape(f, nodes, *w0, d - 1, out);
                shape(f, nodes, *w1, d - 1, out);
            }
        }
        WExpr::Unspecified => out.push(0x00),
    }
}

#[test]
fn tmp_templates() {
    let fc = P256Field::new();
    let curve = Secp256r1::new(&fc);
    let (_c, _st, symbols, info) = compile_with_cert(&fc, |iologic| {
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
        let e = EcdsaCircuit::new(&iologic, &curve);
        let g = circuits_ecdsa2::allocate_given_wires(&iologic, &mut pos);
        let d = circuits_ecdsa2::allocate_derived_wires(&iologic, &mut pos);
        (e.assert_signature(&g, &d), 1, 0)
    });
    // (1) distinct assertion path strings
    let mut paths: HashMap<String, usize> = HashMap::new();
    for rec in &info.assertions {
        for p in symbols.tracker().group_paths(rec.id) {
            *paths.entry(p).or_insert(0) += 1;
        }
    }
    let mut byname: HashMap<String, usize> = HashMap::new();
    for (p, c) in &paths {
        let leaf = p.rsplit('/').next().unwrap().to_string();
        *byname.entry(leaf).or_insert(0) += c;
    }
    println!(
        "PATHS instances={} distinct_strings={} distinct_leaf_names={}",
        info.assertions.len(),
        paths.len(),
        byname.len()
    );
    let mut v: Vec<_> = byname.iter().collect();
    v.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
    for (n, c) in v.iter().take(14) {
        println!("  LEAF {n} x{c}");
    }

    // (2) structural template multiplicity of asserted sub-DAGs, by depth
    for d in [2usize, 4, 6, 8] {
        let mut tmpl: HashMap<Vec<u8>, usize> = HashMap::new();
        for rec in &info.assertions {
            let mut k = Vec::new();
            shape(&fc, &info.nodes, rec.asserted_node as usize, d, &mut k);
            *tmpl.entry(k).or_insert(0) += 1;
        }
        let mut mult: Vec<usize> = tmpl.values().copied().collect();
        mult.sort_unstable_by(|a, b| b.cmp(a));
        println!(
            "TEMPLATES depth={d} distinct={} ratio={:.1}x top={:?}",
            tmpl.len(),
            info.assertions.len() as f64 / tmpl.len() as f64,
            &mult[..mult.len().min(8)]
        );
    }
}
