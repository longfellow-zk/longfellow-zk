// Read-only inspector: `Lfzk.Arith`'s structural hypotheses (`Isolated`, `DeadEnd`, and
// `Lfzk.ZkArithProfile.WellFormedP` at the circuit's own width profile) on the
// REGISTERED mdoc circuits of one version (default the deployed v7), loaded from the stored
// artifacts exactly as `inspect_v7_circuit_profile.rs` loads them (registry combined hash, entry
// IDs recomputed from the parsed circuits, the runtime's own `decompress_circuits`).  The Python
// driver `inspect_v7_assertions.py` builds this file in a temporary Cargo package.
use core_algebra::field::AlgebraicField;
use core_proto::{archive::compute_combined_id, circuit::compute_id, reader::CircuitReader};
use runtime_algebra::{gf2_128::Gf2_128Field, p256::P256Field};
use std::collections::{HashMap, HashSet};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let version: usize = args.get(1).map_or(7, |s| s.parse().unwrap());

    let p256 = P256Field::new();
    let gf2 = Gf2_128Field::new();

    let mut sig_id: Option<[u8; 32]> = None;
    for attributes in 1..=4 {
        let provided = mdoc_zk_runtime::materialize(version, attributes)
            .unwrap_or_else(|e| panic!("materialize({version}, {attributes}): {e:?}"));
        let spec = provided.spec;
        assert_eq!(spec.version, version);
        assert_eq!(spec.num_attributes, attributes);
        let archive = &provided.archive;
        assert_eq!(archive.combined_id, spec.combined_hash, "archive id != registry hash");
        assert_eq!(
            compute_combined_id(&archive.entries),
            spec.combined_hash,
            "combined id of the entries != registry hash"
        );
        assert_eq!(provided.name, spec.combined_hash_hex());

        let sig_entry = archive.get("sig").expect("sig entry");
        let hash_entry = archive.get("hash").expect("hash entry");
        let (c_sig, rest) = CircuitReader::new(&p256, core_proto::FieldID::P256)
            .from_bytes(&sig_entry.payload, true)
            .expect("sig circuit parses with its ID enforced");
        assert!(rest.is_empty());
        let (c_hash, rest) = CircuitReader::new(&gf2, core_proto::FieldID::Gf2_128)
            .from_bytes(&hash_entry.payload, true)
            .expect("hash circuit parses with its ID enforced");
        assert!(rest.is_empty());
        assert_eq!(c_sig.id, sig_entry.circuit_id);
        assert_eq!(c_hash.id, hash_entry.circuit_id);
        assert_eq!(compute_id(&p256, &c_sig.raw), sig_entry.circuit_id);
        assert_eq!(compute_id(&gf2, &c_hash.raw), hash_entry.circuit_id);

        // the runtime's own loading path
        let (r_sig, r_hash) =
            mdoc_zk_runtime::decompress_circuits(&provided.compressed, &p256, &gf2)
                .expect("decompress_circuits");
        assert_eq!(compute_id(&p256, &r_sig.raw), sig_entry.circuit_id);
        assert_eq!(compute_id(&gf2, &r_hash.raw), hash_entry.circuit_id);

        println!(
            "ARCHIVE {} {} version={} circuit_version={} combined={} sig_id={} hash_id={} \
             ligero_hash=({},{},{}) ligero_sig=({},{},{})",
            attributes,
            spec.system,
            spec.version,
            archive.circuit_version,
            hex(&spec.combined_hash),
            hex(&sig_entry.circuit_id),
            hex(&hash_entry.circuit_id),
            spec.ligero_hash.rateinv,
            spec.ligero_hash.nreq,
            spec.ligero_hash.block_enc,
            spec.ligero_sig.rateinv,
            spec.ligero_sig.nreq,
            spec.ligero_sig.block_enc,
        );

        if sig_id.is_none() {
            report("sig", 0, &c_sig.raw, &p256);
            sig_id = Some(sig_entry.circuit_id);
        } else {
            assert_eq!(sig_id, Some(sig_entry.circuit_id), "signature circuit differs");
        }

        report("hash", attributes, &c_hash.raw, &gf2);
    }
}

fn report<F: core_algebra::SerializableField + AlgebraicField>(
    component: &str,
    attributes: usize,
    raw: &core_proto::circuit::RawCircuit<F>,
    f: &F,
) {
    let nl = raw.layers.len();
    let terms: Vec<Vec<core_proto::circuit::Term<F>>> =
        raw.layers.iter().map(|l| l.terms(&raw.constants)).collect();
    let mut assert_wires: Vec<HashSet<u32>> = vec![HashSet::new(); nl + 1];
    let mut per_layer = Vec::new();
    let mut non_isolated = 0usize;
    for ly in 0..nl {
        let mut gcount: HashMap<u32, usize> = HashMap::new();
        for t in &terms[ly] {
            *gcount.entry(t.g).or_insert(0) += 1;
        }
        let mut na = 0usize;
        for t in &terms[ly] {
            if f.is_zero(&t.k) {
                na += 1;
                assert_wires[ly].insert(t.g);
                if gcount[&t.g] != 1 {
                    non_isolated += 1;
                }
            }
        }
        per_layer.push(na);
    }
    let mut dead_end_violations = 0usize;
    for ly in 0..nl {
        for t in &terms[ly] {
            if assert_wires[ly + 1].contains(&t.h0) || assert_wires[ly + 1].contains(&t.h1) {
                dead_end_violations += 1;
            }
        }
    }
    // `Lfzk.ZkArithProfile.WellFormedP` at the circuit's own profile: a layer; every term of layer
    // `ly` has its output corner below `2^ow(ly)` (`ow 0 = logv`, `ow (ly+1) = logw ly`) and its hand
    // corners below `2^logw(ly)`; the inputs fit the last layer's hand cube.
    let mut wf_violations = 0usize;
    if nl == 0 {
        wf_violations += 1;
    }
    for ly in 0..nl {
        let lw = raw.layers[ly].logw();
        let ow = if ly == 0 { raw.logv } else { raw.layers[ly - 1].logw() };
        for t in &terms[ly] {
            if (t.g as u64) >= (1u64 << ow)
                || (t.h0 as u64) >= (1u64 << lw)
                || (t.h1 as u64) >= (1u64 << lw)
            {
                wf_violations += 1;
            }
        }
    }
    if nl > 0 && (raw.ninput as u64) > (1u64 << raw.layers[nl - 1].logw()) {
        wf_violations += 1;
    }
    let total: usize = per_layer.iter().sum();
    let by_layer: Vec<String> = per_layer
        .iter()
        .enumerate()
        .filter(|(_, &n)| n > 0)
        .map(|(i, n)| format!("{}:{}", i, n))
        .collect();
    println!(
        "ASSERTS {} {} nl={} logv={} total_asserts={} by_layer=[{}] non_isolated={} dead_end_violations={} wf_violations={}",
        component,
        attributes,
        nl,
        raw.logv,
        total,
        by_layer.join(","),
        non_isolated,
        dead_end_violations,
        wf_violations
    );
}
