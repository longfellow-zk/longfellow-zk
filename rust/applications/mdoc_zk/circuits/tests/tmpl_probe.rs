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
use compile_algebra::gf2_128::Gf2_128Field;
use compile_compiler::{compile_with_cert, quad::WExpr};
use core_algebra::SerializableField;
use mdoc_zk_circuits::mso_attribute::circuit::AttributeVerifier;
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
fn mso_attribute_templates() {
    let fc = Gf2_128Field::new();
    let (_c, _geo, symbols, info) = compile_with_cert(&fc, |iologic| {
        let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
        let verifier = AttributeVerifier::new(&iologic);
        let bv = circuits_bitvec::BitvecLogic::new(&iologic);
        let given = mdoc_zk_circuits::mso_attribute::allocate_given(&bv, &mut pos);
        let derived = mdoc_zk_circuits::mso_attribute::allocate_derived(&bv, &mut pos);
        (verifier.assert_attribute(&given, &derived), 1, 0)
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

/// The question this whole exercise turns on: `mdoc_hash` is ~44 SHA blocks' worth of
/// assertions (303,413 against one block's ~6,840). If those copies collapse to the same
/// templates, then `Backed`+`Asserts` -- 46.6% of the SHA-256 build, and the largest projected
/// cost for mdoc -- is mostly redundant work. If they do not, mdoc really is 44 distinct
/// circuits and the projection stands.
#[test]
fn mdoc_hash_templates() {
    use compile_algebra::CompileNat;
    use mdoc_zk_circuits::{
        hash::{hash_input_of_parsed_mdoc, MdocHash},
        parse_test_data,
    };

    let fc = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);
    let num_attrs = hash_input.attrs.len();
    let mut pos = compile_logic::K_FIRST_WIRE_POSITION;

    let (_c, _geo, symbols, info) = compile_with_cert(&fc, |iologic| {
        let mdoc = MdocHash::new(&iologic, num_attrs);
        let bv = circuits_bitvec::BitvecLogic::new(&iologic);
        let given = mdoc_zk_circuits::hash::allocate_given(&iologic, &bv, num_attrs, &mut pos);
        let derived = mdoc_zk_circuits::hash::allocate_derived::<
            _,
            { mdoc_zk_circuits::hash::constants::K_MAX_SHA_BLOCKS },
        >(&bv, num_attrs, &mut pos);
        (
            mdoc.assert_valid_presentation_and_macs(&given, &derived),
            1,
            0,
        )
    });

    println!(
        "MDOC-HASH nodes={} assertions={}",
        info.nodes.len(),
        info.assertions.len()
    );

    let mut memo = HashMap::new();
    let mut tmpl: HashMap<u64, usize> = HashMap::new();
    for rec in &info.assertions {
        let s = sig(&fc, &info.nodes, rec.asserted_node as usize, &mut memo);
        *tmpl.entry(s).or_insert(0) += 1;
    }
    let mut mult: Vec<usize> = tmpl.values().copied().collect();
    mult.sort_unstable_by(|a, b| b.cmp(a));
    let singles = mult.iter().filter(|&&m| m == 1).count();
    println!(
        "ASSERT-TMPL distinct={} instances={} ratio={:.1}x singletons={} ({:.0}%)",
        tmpl.len(),
        info.assertions.len(),
        info.assertions.len() as f64 / tmpl.len() as f64,
        singles,
        100.0 * singles as f64 / tmpl.len() as f64
    );
    println!("  top: {:?}", &mult[..mult.len().min(10)]);

    // The assertion scope tree: the compiler's own account of what the circuit proves.
    // Distinct path prefixes by depth are the obligation hierarchy a spec has to cover.
    {
        let mut bydepth: Vec<HashMap<String, usize>> = vec![HashMap::new(); 5];
        for rec in &info.assertions {
            for path in symbols.tracker().group_paths(rec.id) {
                let segs: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
                for d in 0..bydepth.len().min(segs.len()) {
                    *bydepth[d].entry(segs[..=d].join("/")).or_insert(0) += 1;
                }
            }
        }
        for (d, m) in bydepth.iter().enumerate() {
            if m.is_empty() { continue; }
            let mut v: Vec<_> = m.iter().collect();
            v.sort_by_key(|(k, c)| (std::cmp::Reverse(**c), (*k).clone()));
            println!("SCOPE depth {} : {} distinct", d + 1, m.len());
            for (k, c) in v.iter().take(if d < 2 { 14 } else { 8 }) {
                println!("   {c:>7}  {k}");
            }
        }
    }

    // Backed's scan work: sum over assertions of |azt(its wireLayer)|, where azt(L) is the
    // count of assertions whose wire sits on layer L. backedRawWith scans that list per
    // assertion, so this is quadratic in the per-layer assertion count.
    let mut perlayer: HashMap<usize, usize> = HashMap::new();
    for rec in &info.assertions {
        *perlayer.entry(rec.wire.layer).or_insert(0) += 1;
    }
    let mut pl: Vec<_> = perlayer.iter().map(|(a, b)| (*a, *b)).collect();
    pl.sort();
    let work: u64 = pl.iter().map(|(_, c)| (*c as u64) * (*c as u64)).sum();
    println!("BACKED layers={} scan_work={work}  (= sum_L n_L^2)", pl.len());
    for (l, c) in pl.iter() {
        println!("  layer {l:>3} : {c:>7} assertions -> {:>15} comparisons", (*c as u64) * (*c as u64));
    }

    // cone-size distribution: what the meaning layer actually pays per assertion
    let mut hist: HashMap<usize, usize> = HashMap::new();
    let mut summed = 0usize;
    for rec in &info.assertions {
        let mut seen = std::collections::HashSet::new();
        cone(&info.nodes, rec.asserted_node as usize, &mut seen);
        summed += seen.len();
        *hist.entry(seen.len()).or_insert(0) += 1;
    }
    let mut hv: Vec<_> = hist.into_iter().collect();
    hv.sort_by_key(|(sz, _)| *sz);
    println!(
        "CONE-DIST summed={summed} assertions={} mean={:.1}",
        info.assertions.len(),
        summed as f64 / info.assertions.len() as f64
    );
    for (sz, c) in hv.iter().take(6) {
        println!("  {sz:>5} nodes : {c:>7} assertions");
    }
    println!("  ... {} distinct cone sizes; largest {}", hv.len(), hv.last().unwrap().0);
    let sumsq: f64 = hv.iter().map(|(sz, c)| (*sz as f64) * (*sz as f64) * (*c as f64)).sum();
    let tail: usize = hv.iter().filter(|(sz, _)| *sz > 3).map(|(_, c)| *c).sum();
    let tailnodes: usize = hv.iter().filter(|(sz, _)| *sz > 3).map(|(sz, c)| sz * c).sum();
    println!("CONE-SQ sum_n2={sumsq:.3e}  tail(>3): {tail} assertions, {tailnodes} cone-nodes");

    // node level, which is what the structural checks walk
    let mut by: HashMap<u64, usize> = HashMap::new();
    for i in 0..info.nodes.len() {
        let s = sig(&fc, &info.nodes, i, &mut memo);
        *by.entry(s).or_insert(0) += 1;
    }
    let rep: usize = by.values().filter(|&&c| c > 1).sum();
    println!(
        "NODE-TMPL distinct={} nodes={} ratio={:.1}x in-repeated={:.0}%",
        by.len(),
        info.nodes.len(),
        info.nodes.len() as f64 / by.len() as f64,
        100.0 * rep as f64 / info.nodes.len() as f64
    );
}

/// How well does LFC2 actually compress the repeated structure?
///
/// SHA-256 *one block* compresses only 3.4x (472,456 expanded numbers -> 139,684 in
/// segments+deltas+tokens), because a single block has little to repeat. mdoc_hash is ~40 blocks,
/// so this is the number that decides whether "prove against the compressed form" is worth
/// anything: bytes per term is the fair comparison across circuits of different size.
#[test]
fn lfc2_compression() {
    use compile_eval::FieldID;
    use core_proto::writer::CircuitWriter;
    use mdoc_zk_circuits::{
        hash::{hash_input_of_parsed_mdoc, MdocHash},
        parse_test_data,
    };
    use compile_algebra::CompileNat;

    let fc = Gf2_128Field::new();
    let (_, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let hash_input = hash_input_of_parsed_mdoc(&parsed, &parsed.all_attr_ids(), now);
    let num_attrs = hash_input.attrs.len();
    let mut pos = compile_logic::K_FIRST_WIRE_POSITION;

    let (circuit, geo, _sym) = compile_compiler::compile(&fc, |iologic| {
        let mdoc = MdocHash::new(&iologic, num_attrs);
        let bv = circuits_bitvec::BitvecLogic::new(&iologic);
        let given = mdoc_zk_circuits::hash::allocate_given(&iologic, &bv, num_attrs, &mut pos);
        let derived = mdoc_zk_circuits::hash::allocate_derived::<
            _,
            { mdoc_zk_circuits::hash::constants::K_MAX_SHA_BLOCKS },
        >(&bv, num_attrs, &mut pos);
        (
            mdoc.assert_valid_presentation_and_macs(&given, &derived),
            1,
            0,
        )
    });

    let w = CircuitWriter::new(&fc, FieldID::Gf2_128);
    let l1 = w.to_bytes_lfc1(&circuit).len();
    let flat = l1;
    let l2 = w.to_bytes_lfc2(&circuit).len();
    let l3 = w.to_bytes_lfc2(&circuit).len();
    let nterms = geo.nterms;

    println!("MDOC-HASH terms={nterms}  (LFC1 is the uncompressed baseline)");
    println!("  LFC1   {l1:>10} bytes  = {:.3} B/term", l1 as f64 / nterms as f64);
    println!("  flat   {flat:>10} bytes  = {:.3} B/term", flat as f64 / nterms as f64);
    println!("  LFC2   {l2:>10} bytes  = {:.3} B/term  ({:.1}x vs flat)",
             l2 as f64 / nterms as f64, flat as f64 / l2 as f64);
    println!("  LFC2   {l3:>10} bytes  = {:.3} B/term  ({:.1}x vs flat)",
             l3 as f64 / nterms as f64, flat as f64 / l3 as f64);
    println!("  SHA-256 one block for reference: 118114 terms, LFC2 203326 B = 1.721 B/term");
}
