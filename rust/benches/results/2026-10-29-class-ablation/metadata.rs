use std::{fs, path::Path};

use longfellow_zk::{
    core::{
        algebra::SerializableField,
        proto::{archive::CircuitArchive, circuit::Circuit, reader::CircuitReader, FieldID},
    },
    runtime::algebra::{fp24_ext6::RuntimeFp24Ext6, gf2_128::Gf2_128Field, p256::P256Field},
};
fn show<F: SerializableField>(
    case: &str,
    app: &str,
    component: &str,
    c: &Circuit<F>,
    geometry: &mut String,
    terms: &mut String,
) {
    let slots = c.raw.layers.iter().map(|l| l.nw()).sum::<usize>();
    let total = c.raw.layers.iter().map(|l| l.num_terms()).sum::<usize>();
    geometry.push_str(&format!(
        "{case},{app},{component},{},{},{},{},{},{},{}\n",
        c.raw.ninput,
        c.raw.npublic_input,
        c.raw.noutput,
        slots,
        slots + c.raw.noutput - c.raw.ninput,
        c.raw.layers.len(),
        total
    ));
    let mut counts = [[0usize; 4]; 3];
    for l in &c.raw.layers {
        for (d, s) in l.streams().enumerate() {
            s.for_each_delta_index(|_| counts[d][3] += 1);
            if let Some(c) = s.coefficients() {
                counts[d][0] += c.assertions.num_terms();
                counts[d][1] += c.units.num_terms();
                counts[d][2] += c.negatives.num_terms();
            }
        }
    }
    for (d, kind) in ["quadratic", "linear", "constant"].into_iter().enumerate() {
        terms.push_str(&format!(
            "{case},{app},{component},{kind},{},{},{},{}\n",
            counts[d][0], counts[d][1], counts[d][2], counts[d][3]
        ));
    }
}
fn main() {
    let root = Path::new("/tmp/longfellow-ablation");
    let mut geometry=String::from("case,application,component,inputs,public_inputs,outputs,layer_input_slots,wires,layers,terms\n");
    let mut terms=String::from("case,application,component,v2,assertion_array,one_array,minus_one_array,general_array\n");
    for case in ["legacy", "degree", "zero", "one", "minus", "all"] {
        for n in [2, 4] {
            let b = fs::read(
                root.join(case)
                    .join(format!("v9/v9-uniform-inputs-{n}-0.cache")),
            )
            .unwrap();
            assert_eq!(&b[..8], b"MDOCBIT6");
            let len = u64::from_le_bytes(b[120..128].try_into().unwrap()) as usize;
            let raw = zstd::decode_all(&b[128 + len..]).unwrap();
            let archive = CircuitArchive::from_bytes(&raw).unwrap();
            let app = format!("v9-{n}");
            let p = P256Field::new();
            let f = Gf2_128Field::new();
            let (c, tail) = CircuitReader::new(&p, FieldID::P256)
                .from_bytes(&archive.entries[0].payload, true)
                .unwrap();
            assert!(tail.is_empty());
            show(case, &app, "signature", &c, &mut geometry, &mut terms);
            let (c, tail) = CircuitReader::new(&f, FieldID::Gf2_128)
                .from_bytes(&archive.entries[1].payload, true)
                .unwrap();
            assert!(tail.is_empty());
            show(case, &app, "hash", &c, &mut geometry, &mut terms);
        }
        for n in [44, 65] {
            let f = RuntimeFp24Ext6::new();
            let raw = fs::read(root.join(case).join(format!("mldsa/MlDsa{n}.lfc2"))).unwrap();
            let (c, tail) = CircuitReader::new(&f, FieldID::None)
                .from_bytes(&raw, true)
                .unwrap();
            assert!(tail.is_empty());
            show(
                case,
                &format!("mldsa-{n}"),
                "verifier",
                &c,
                &mut geometry,
                &mut terms,
            );
        }
    }
    fs::write(root.join("geometry.csv"), &geometry).unwrap();
    fs::write(root.join("terms.csv"), terms).unwrap();
    let rows: Vec<Vec<&str>> = geometry
        .lines()
        .skip(1)
        .map(|l| l.split(',').collect())
        .collect();
    for app in ["v9-2", "v9-4", "mldsa-44", "mldsa-65"] {
        for component in ["signature", "hash", "verifier"] {
            let selected: Vec<_> = rows
                .iter()
                .filter(|r| {
                    r[1] == app
                        && r[2] == component
                        && ["zero", "one", "minus", "all"].contains(&r[0])
                })
                .collect();
            if selected.is_empty() {
                continue;
            }
            assert_eq!(selected.len(), 4);
            assert!(
                selected.iter().all(|r| r[3..] == selected[0][3..]),
                "geometry differs: {app} {component}"
            );
        }
    }
    println!("Validated IDs and identical geometry for all four controlled coefficient policies.");
}
