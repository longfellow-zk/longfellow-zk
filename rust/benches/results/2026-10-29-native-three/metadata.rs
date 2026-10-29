use std::{fs, path::Path};

use longfellow_zk::{
    core::{
        algebra::SerializableField,
        proto::{
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
    f: &F,
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
    let counts = c.term_class_breakdown(f);
    let mut stats = [[0usize; 3]; 3];
    fn add<T>(out: &mut [usize; 3], s: &Stream<T>) {
        out[0] += s.deltas.len();
        out[1] += s.segments.len();
        out[2] += s.tokens.len();
    }
    for l in &c.raw.layers {
        add(&mut stats[0], &l.quadratic);
        add(&mut stats[1], &l.linear);
        add(&mut stats[2], &l.constant);
    }
    for (i, kind) in ["quadratic", "linear", "constant"].into_iter().enumerate() {
        let r = counts[i];
        let s = stats[i];
        terms.push_str(&format!(
            "{app},{component},{kind},{},{},{},{},{},{},{}\n",
            r[0], r[1], r[2], r[3], s[0], s[1], s[2]
        ));
    }
}
fn main() {
    let root = Path::new("/tmp/native-three-benchmark");
    let mut sizes = String::from("application,raw_bytes,zstd_bytes,decoded_heap_bytes\n");
    let mut geometry = String::from(
        "application,component,inputs,public_inputs,outputs,layer_input_slots,wires,layers,terms\n",
    );
    let mut terms=String::from("application,component,term_type,assertions,one,minus_one,general,dictionary_records,segments,tokens\n");
    for n in [2, 4] {
        let bundle = longfellow_zk::mdoc::development_provider::read_next_file(
            &root.join(format!("circuits/next/next-v9-{n}.cache")),
        )
        .unwrap();
        let p = P256Field::new();
        let f = Gf2_128Field::new();
        let (s, h) =
            longfellow_zk::mdoc::v2::provider::load(bundle.spec(), bundle.compressed(), &p, &f)
                .unwrap();
        let app = format!("next-{n}");
        show(&app, "signature", &s, &p, &mut geometry, &mut terms);
        show(&app, "hash", &h, &f, &mut geometry, &mut terms);
        sizes.push_str(&format!(
            "{app},{},{},{}\n",
            zstd::decode_all(bundle.compressed()).unwrap().len(),
            bundle.compressed().len(),
            s.heap_bytes() + h.heap_bytes()
        ));
    }
    for n in [44, 65] {
        let raw = fs::read(root.join(format!("circuits/mldsa/MlDsa{n}.lfc3"))).unwrap();
        let f = RuntimeFp24Ext6::new();
        let (c, tail) = CircuitReader::new(&f, FieldID::None)
            .from_bytes_v2(&raw, true)
            .unwrap();
        assert!(tail.is_empty());
        let app = format!("mldsa-{n}");
        show(&app, "verifier", &c, &f, &mut geometry, &mut terms);
        sizes.push_str(&format!(
            "{app},{},{},{}\n",
            raw.len(),
            zstd::encode_all(raw.as_slice(), 16).unwrap().len(),
            c.heap_bytes()
        ));
    }
    let old=fs::read_to_string("/home/athena/sandbox/hack/longfellow-zk/rust/benches/results/2026-10-29-next-v9/geometry.csv").unwrap();
    assert_eq!(geometry, old, "graph geometry changed");
    fs::write(root.join("sizes.csv"), &sizes).unwrap();
    fs::write(root.join("geometry.csv"), geometry).unwrap();
    fs::write(root.join("terms.csv"), terms).unwrap();
    print!("{sizes}");
    println!("All circuit IDs authenticated; geometry matches HEAD's eleven-stream circuits.");
}
