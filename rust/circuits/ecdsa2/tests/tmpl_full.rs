//! Does `mso_attribute`'s 3x reuse of the SHA-256 primitive survive compilation as three
//! structurally identical regions?
//!
//! `tests/tmp_tmpl.rs` in ecdsa2 answers the same question with a *tree* expansion of the DAG to
//! a fixed depth, which is exponential and so cannot reach full cone depth -- it saturates around
//! depth 8. This uses a memoised structural hash instead: linear, and it classifies each asserted
//! node by its whole cone.
//!
//! `Input` hashes to a constant, so two regions fed by different wires collide iff they are
//! isomorphic under a renaming of their inputs. That is exactly "the same subcircuit instantiated
//! at an offset". Constants are folded into the hash, so copies that differ in a round constant
//! are correctly counted apart.
use compile_algebra::{p256::P256Field, secp256r1::Secp256r1};
use compile_compiler::{compile_with_cert, quad::WExpr};
use core_algebra::SerializableField;
use circuits_ecdsa2::EcdsaCircuit;
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

/// Structural signature of the cone rooted at `n`, to full depth, memoised.
fn sig<F: compile_algebra::field::CompileField + SerializableField>(
    f: &F,
    nodes: &[WExpr<F>],
    n: usize,
    memo: &mut HashMap<usize, u64>,
) -> u64 {
    if let Some(h) = memo.get(&n) {
        return *h;
    }
    // Placeholder guards against cycles; the DAG is acyclic, so it should never be read.
    memo.insert(n, 0);
    let mut h = DefaultHasher::new();
    match &nodes[n] {
        WExpr::Input { .. } => 0x01u8.hash(&mut h),
        WExpr::Unspecified => 0x00u8.hash(&mut h),
        WExpr::Assert0(w) => {
            0x02u8.hash(&mut h);
            sig(f, nodes, *w, memo).hash(&mut h);
        }
        WExpr::Sum(ts) => {
            0x03u8.hash(&mut h);
            (ts.len() as u32).hash(&mut h);
            for (k, w0, w1) in ts {
                f.to_bytes(k).hash(&mut h);
                sig(f, nodes, *w0, memo).hash(&mut h);
                sig(f, nodes, *w1, memo).hash(&mut h);
            }
        }
    }
    let v = h.finish();
    memo.insert(n, v);
    v
}

/// As `sig`, but the cone is cut at depth `d`: everything below is one opaque symbol.
fn sigd<F: compile_algebra::field::CompileField + SerializableField>(
    f: &F,
    nodes: &[WExpr<F>],
    n: usize,
    d: usize,
    memo: &mut HashMap<(usize, usize), u64>,
) -> u64 {
    if d == 0 {
        return 0xFFFF_FFFF_FFFF_FFFF;
    }
    if let Some(h) = memo.get(&(n, d)) {
        return *h;
    }
    let mut h = DefaultHasher::new();
    match &nodes[n] {
        WExpr::Input { .. } => 0x01u8.hash(&mut h),
        WExpr::Unspecified => 0x00u8.hash(&mut h),
        WExpr::Assert0(w) => {
            0x02u8.hash(&mut h);
            sigd(f, nodes, *w, d - 1, memo).hash(&mut h);
        }
        WExpr::Sum(ts) => {
            0x03u8.hash(&mut h);
            (ts.len() as u32).hash(&mut h);
            for (k, w0, w1) in ts {
                f.to_bytes(k).hash(&mut h);
                sigd(f, nodes, *w0, d - 1, memo).hash(&mut h);
                sigd(f, nodes, *w1, d - 1, memo).hash(&mut h);
            }
        }
    }
    let v = h.finish();
    memo.insert((n, d), v);
    v
}

/// Cone size (distinct nodes reachable), memoised via a visited set per root.
fn cone<F: compile_algebra::field::CompileField>(
    nodes: &[WExpr<F>],
    n: usize,
    seen: &mut std::collections::HashSet<usize>,
) {
    if !seen.insert(n) {
        return;
    }
    match &nodes[n] {
        WExpr::Input { .. } | WExpr::Unspecified => {}
        WExpr::Assert0(w) => cone(nodes, *w, seen),
        WExpr::Sum(ts) => {
            for (_, w0, w1) in ts {
                cone(nodes, *w0, seen);
                cone(nodes, *w1, seen);
            }
        }
    }
}

#[test]
fn ecdsa2_templates() {
    let fc = P256Field::new();
    let curve = Secp256r1::new(&fc);
    let (_c, _geo, symbols, info) = compile_with_cert(&fc, |iologic| {
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
        let e = EcdsaCircuit::new(&iologic, &curve);
        let g = circuits_ecdsa2::allocate_given_wires(&iologic, &mut pos);
        let d = circuits_ecdsa2::allocate_derived_wires(&iologic, &mut pos);
        (e.assert_signature(&g, &d), 1, 0)
    });
    println!(
        "NODES total={} assertions={}",
        info.nodes.len(),
        info.assertions.len()
    );

    // (1) assertion path leaves -- does the scope tree name the repeated regions?
    let mut byname: HashMap<String, usize> = HashMap::new();
    for rec in &info.assertions {
        for p in symbols.tracker().group_paths(rec.id) {
            let leaf = p.rsplit('/').next().unwrap_or("").to_string();
            *byname.entry(leaf).or_insert(0) += 1;
        }
    }
    let mut v: Vec<_> = byname.iter().collect();
    v.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
    println!("PATH LEAVES distinct={}", byname.len());
    for (n, c) in v.iter().take(12) {
        println!("  LEAF {n} x{c}");
    }

    // (2) full-depth structural classes of asserted cones
    let mut memo = HashMap::new();
    let mut tmpl: HashMap<u64, usize> = HashMap::new();
    for rec in &info.assertions {
        let s = sig(&fc, &info.nodes, rec.asserted_node as usize, &mut memo);
        *tmpl.entry(s).or_insert(0) += 1;
    }
    let mut mult: Vec<usize> = tmpl.values().copied().collect();
    mult.sort_unstable_by(|a, b| b.cmp(a));
    println!(
        "TEMPLATES full-depth distinct={} instances={} ratio={:.1}x",
        tmpl.len(),
        info.assertions.len(),
        info.assertions.len() as f64 / tmpl.len() as f64
    );
    println!("  top multiplicities: {:?}", &mult[..mult.len().min(12)]);
    let singles = mult.iter().filter(|&&m| m == 1).count();
    println!(
        "  classes with 1 instance: {singles} ({:.0}% of classes)",
        100.0 * singles as f64 / tmpl.len() as f64
    );

    // (2b) the same, but with the cone CUT at a fixed depth -- everything below the cut is an
    // opaque variable. This is what templating on declared subcircuit boundaries would give:
    // chained SHA blocks are isomorphic as subcircuits, but their full cones are not, because
    // block k+1's cone swallows block k's.
    for d in [2usize, 4, 6, 8, 12, 16, 24] {
        let mut dmemo: HashMap<(usize, usize), u64> = HashMap::new();
        let mut t: HashMap<u64, usize> = HashMap::new();
        for rec in &info.assertions {
            let s = sigd(&fc, &info.nodes, rec.asserted_node as usize, d, &mut dmemo);
            *t.entry(s).or_insert(0) += 1;
        }
        let singles = t.values().filter(|&&m| m == 1).count();
        println!(
            "CUT depth={d:<3} distinct={:<5} ratio={:>6.1}x  singletons={}",
            t.len(),
            info.assertions.len() as f64 / t.len() as f64,
            singles
        );
    }

    // (3) how much of the circuit do the repeated classes cover?
    let mut total_cone = 0usize;
    let mut rep_cone = 0usize;
    for rec in &info.assertions {
        let mut seen = std::collections::HashSet::new();
        cone(&info.nodes, rec.asserted_node as usize, &mut seen);
        let s = sig(&fc, &info.nodes, rec.asserted_node as usize, &mut memo);
        total_cone += seen.len();
        if tmpl[&s] > 1 {
            rep_cone += seen.len();
        }
    }
    println!(
        "CONES summed={} in-repeated-classes={} ({:.0}%)",
        total_cone,
        rep_cone,
        100.0 * rep_cone as f64 / total_cone.max(1) as f64
    );
}

/// Is the node-index space coverable by few (template, delta) regions?
///
/// `ok`/`corr`/`okInv` walk the whole node list, so exploiting replication for THEM needs the
/// copies to be locatable as index ranges -- not just the assertion cones the sidecar already
/// templates. If the scheduler interleaves copies by layer, a (lo, len, delta) region record is
/// the wrong format and the cover has to be per-layer.
#[test]
fn node_level_replication() {
    let fc = P256Field::new();
    let curve = Secp256r1::new(&fc);
    let (_c, _geo, _symbols, info) = compile_with_cert(&fc, |iologic| {
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
        let e = EcdsaCircuit::new(&iologic, &curve);
        let g = circuits_ecdsa2::allocate_given_wires(&iologic, &mut pos);
        let d = circuits_ecdsa2::allocate_derived_wires(&iologic, &mut pos);
        (e.assert_signature(&g, &d), 1, 0)
    });
    let n = info.nodes.len();
    let mut memo = HashMap::new();
    let mut by: HashMap<u64, Vec<usize>> = HashMap::new();
    for i in 0..n {
        let s = sig(&fc, &info.nodes, i, &mut memo);
        by.entry(s).or_default().push(i);
    }
    let mut classes: Vec<_> = by.values().collect();
    classes.sort_by_key(|v| std::cmp::Reverse(v.len()));
    println!(
        "NODE-SIG total={n} distinct={} ratio={:.1}x",
        by.len(),
        n as f64 / by.len() as f64
    );
    let covered: usize = classes.iter().filter(|v| v.len() > 1).map(|v| v.len()).sum();
    println!(
        "  nodes in classes with >1 member: {covered} ({:.0}%)",
        100.0 * covered as f64 / n as f64
    );
    // For the biggest classes, are the member indices evenly strided?
    for v in classes.iter().take(6) {
        let d: Vec<i64> = v.windows(2).map(|w| w[1] as i64 - w[0] as i64).collect();
        let mut ds: HashMap<i64, usize> = HashMap::new();
        for x in &d {
            *ds.entry(*x).or_insert(0) += 1;
        }
        let mut top: Vec<_> = ds.iter().collect();
        top.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        let top: Vec<String> = top
            .iter()
            .take(3)
            .map(|(delta, c)| format!("{delta}x{c}"))
            .collect();
        println!(
            "  class size={:<5} first={:<6} distinct_deltas={:<4} top_deltas=[{}]",
            v.len(),
            v[0],
            ds.len(),
            top.join(" ")
        );
    }
}
