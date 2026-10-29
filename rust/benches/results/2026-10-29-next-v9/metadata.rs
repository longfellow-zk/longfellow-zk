use std::{fs, path::Path};

use longfellow_zk::{
    core::{
        algebra::SerializableField,
        proto::{
            archive::CircuitArchive,
            reader::CircuitReader,
            v2::{Circuit, Stream},
            FieldID,
        },
    },
    runtime::algebra::{fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field, p256::P256Field},
};
fn show<F: SerializableField>(
    app: &str,
    component: &str,
    c: &Circuit<F>,
    geometry: &mut String,
    terms: &mut String,
) {
    let slots = c.raw.layers.iter().map(|l| l.nw).sum::<usize>();
    geometry.push_str(&format!(
        "{app},{component},{},{},{},{},{},{},{}\n",
        c.raw.ninput,
        c.raw.npublic_input,
        c.raw.noutput,
        slots,
        slots + c.raw.noutput - c.raw.ninput,
        c.raw.layers.len(),
        c.raw.layers.iter().map(|l| l.num_terms()).sum::<usize>()
    ));
    let mut rows = [[0usize; 7]; 3];
    fn add<T>(row: &mut [usize; 7], class: usize, s: &Stream<T>) {
        row[class] += s.num_terms();
        row[4] += s.deltas.len();
        row[5] += s.segments.len();
        row[6] += s.tokens.len();
    }
    for l in &c.raw.layers {
        add(&mut rows[0], 0, &l.quadratic_assertions);
        add(&mut rows[0], 1, &l.quadratic_one);
        add(&mut rows[0], 2, &l.quadratic_minus_one);
        add(&mut rows[0], 3, &l.quadratic);
        add(&mut rows[1], 0, &l.linear_assertions);
        add(&mut rows[1], 1, &l.linear_one);
        add(&mut rows[1], 2, &l.linear_minus_one);
        add(&mut rows[1], 3, &l.linear);
        add(&mut rows[2], 1, &l.constant_one);
        add(&mut rows[2], 2, &l.constant_minus_one);
        add(&mut rows[2], 3, &l.constant);
    }
    for (kind, row) in ["quadratic", "linear", "constant"].into_iter().zip(rows) {
        terms.push_str(&format!(
            "{app},{component},{kind},{},{},{},{},{},{},{}\n",
            row[0], row[1], row[2], row[3], row[4], row[5], row[6]
        ));
    }
}
fn main() {
    let root = Path::new("/tmp/next-v9-benchmark");
    let mut geometry = String::from(
        "application,component,inputs,public_inputs,outputs,layer_input_slots,wires,layers,terms\n",
    );
    let mut terms=String::from("application,component,term_type,assertions,one,minus_one,general,dictionary_records,segments,tokens\n");
    let mut sizes = String::from("application,raw_bytes,zstd_bytes,decoded_heap_bytes\n");
    for n in [2, 4] {
        let bundle = longfellow_zk::mdoc::development_provider::read_next_file(
            &root.join(format!("circuits/next/next-v9-{n}.cache")),
        )
        .unwrap();
        let raw = zstd::decode_all(bundle.compressed()).unwrap();
        assert_eq!(&raw[..4], b"LFA2");
        let a = CircuitArchive::from_bytes(&raw).unwrap();
        assert_eq!(a.circuit_version, 9);
        assert!(a.entries[..2].iter().all(|e| &e.payload[..4] == b"LFC3"));
        let p = P256Field::new();
        let f = Gf2_128Field::new();
        let (s, h) =
            longfellow_zk::mdoc::v2::provider::load(bundle.spec(), bundle.compressed(), &p, &f)
                .unwrap();
        let app = format!("next-{n}");
        show(&app, "signature", &s, &mut geometry, &mut terms);
        show(&app, "hash", &h, &mut geometry, &mut terms);
        sizes.push_str(&format!(
            "{app},{},{},{}\n",
            raw.len(),
            bundle.compressed().len(),
            s.heap_bytes() + h.heap_bytes()
        ));
    }
    for n in [44, 65] {
        let f = RuntimeFp24Ext6::new();
        let raw = fs::read(root.join(format!("circuits/mldsa/MlDsa{n}.lfc3"))).unwrap();
        let (c, tail) = CircuitReader::new(&f, FieldID::None)
            .from_bytes_lfc3(&raw, true)
            .unwrap();
        assert!(tail.is_empty());
        let app = format!("mldsa-{n}");
        show(&app, "verifier", &c, &mut geometry, &mut terms);
        sizes.push_str(&format!(
            "{app},{},{},{}\n",
            raw.len(),
            zstd::encode_all(raw.as_slice(), 16).unwrap().len(),
            c.heap_bytes()
        ));
    }
    let old = fs::read_to_string("/tmp/longfellow-ablation/geometry.csv").unwrap();
    for row in geometry.lines().skip(1) {
        let fields: Vec<_> = row.split(',').collect();
        let name = fields[0].replace("next-", "v9-");
        let expected = old
            .lines()
            .skip(1)
            .map(|r| r.split(',').collect::<Vec<_>>())
            .find(|r| r[0] == "all" && r[1] == name && r[2] == fields[1])
            .unwrap();
        assert_eq!(
            &fields[2..],
            &expected[3..],
            "geometry changed: {} {}",
            fields[0],
            fields[1]
        );
    }
    fs::write(root.join("geometry.csv"), geometry).unwrap();
    fs::write(root.join("terms.csv"), terms).unwrap();
    fs::write(root.join("sizes.csv"), &sizes).unwrap();
    print!("{sizes}");
    println!("All circuit IDs verified; geometry matches the earlier full-class circuits.");
}
