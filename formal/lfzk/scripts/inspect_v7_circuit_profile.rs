// Read-only inspector: the sumcheck layer profile and the Ligero geometry of the REGISTERED mdoc
// circuits of one version (default 7), loaded from the stored artifacts exactly as the deployed
// runtime loads them.  The Python driver `inspect_v7_circuit_profile.py` builds this file in a
// temporary Cargo package against the checked-out Rust workspace; nothing in the repository is
// written.
//
// For each attribute count `1..=4`:
//   * `mdoc_zk_runtime::materialize(version, attributes)` finds the `ZK_SPECS` record and reads
//     `rust/applications/mdoc_zk/artifacts/circuits/<combined_hash>.lfa2` (zstd, LFA2 archive);
//   * the archive's `combined_id`, and `compute_combined_id` of its entries, must equal the
//     registry's `combined_hash`;
//   * both entries are parsed with `enforce_circuit_id = true` (the reader recomputes the circuit
//     ID from the parsed circuit), and the computed ID must equal the entry's recorded ID;
//   * the runtime's own `decompress_circuits` must give the same IDs;
//   * the deployed verifier's `ZkVerifier::geometry` gives the Ligero geometry (`block`,
//     `dblock`, `block_enc`, `nreq`, `nrow`) and the sumcheck `logw_layers`, which must agree
//     with the parsed layers.
// The signature circuit is the same in all four archives (checked by ID) and is reported once.
use core_proto::{archive::compute_combined_id, circuit::compute_id, reader::CircuitReader};
use runtime_algebra::{
    gf2_128::Gf2_128Field, lch14_reed_solomon::Lch14InterpolatorFactory, p256::P256Field,
    reed_solomon::FftInterpolatorFactory, SupportsFFT,
};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let version: usize = args.get(1).map_or(7, |s| s.parse().unwrap());

    let p256 = P256Field::new();
    let p256_2 = runtime_algebra::fp2::Fp2Field::new(&p256);
    let omega = p256_2.omega();
    let omega_order = p256_2.omega_order();
    let make_interpolator_sig = FftInterpolatorFactory::new(&p256, &p256_2, omega, omega_order);
    let gf2 = Gf2_128Field::new();
    let sf_hash =
        runtime_algebra::subfield::BinarySubfield::new(&core_algebra::proto::GF2_16_BASIS_V1);
    let make_interpolator_hash = Lch14InterpolatorFactory::new(&gf2, &sf_hash);

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
            report("sig", 0, &c_sig.raw, &hex(&sig_entry.circuit_id));
            let v = runtime_zk::ZkVerifier::<4, _>::new(c_sig, spec.ligero_sig);
            let g = v.geometry(&runtime_zk::common::ZkContext {
                f: &p256,
                make_interpolator: &make_interpolator_sig,
            });
            report_geometry("sig", 0, &g);
            sig_id = Some(sig_entry.circuit_id);
        } else {
            assert_eq!(sig_id, Some(sig_entry.circuit_id), "signature circuit differs");
        }

        report("hash", attributes, &c_hash.raw, &hex(&hash_entry.circuit_id));
        let v = runtime_zk::ZkVerifier::<2, _>::new(c_hash, spec.ligero_hash);
        let g = v.geometry(&runtime_zk::common::ZkContext {
            f: &gf2,
            make_interpolator: &make_interpolator_hash,
        });
        report_geometry("hash", attributes, &g);
    }
}

fn report<F: core_proto::SerializableField>(
    component: &str,
    attributes: usize,
    raw: &core_proto::circuit::RawCircuit<F>,
    id: &str,
) {
    let logw: Vec<String> = raw.layers.iter().map(|l| l.logw().to_string()).collect();
    let nw: Vec<String> = raw.layers.iter().map(|l| l.nw().to_string()).collect();
    println!(
        "PROFILE {} {} logv={} npublic={} nlayers={} logw=[{}] nw=[{}] ninput={} id={}",
        component,
        attributes,
        raw.logv,
        raw.npublic_input,
        raw.layers.len(),
        logw.join(","),
        nw.join(","),
        raw.ninput,
        id
    );
}

fn report_geometry(component: &str, attributes: usize, g: &runtime_proto::ZkProofGeometry) {
    let logw: Vec<String> = g.sc_geom.logw_layers.iter().map(ToString::to_string).collect();
    let c = &g.com_geom;
    println!(
        "GEOMETRY {} {} block={} dblock={} block_enc={} nreq={} r={} nrow={} mc_pathlen={} \
         logw=[{}]",
        component,
        attributes,
        c.block,
        c.dblock,
        c.block_enc,
        c.nreq,
        c.r,
        c.nrow,
        c.mc_pathlen,
        logw.join(",")
    );
}
