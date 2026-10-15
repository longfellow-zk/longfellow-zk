//! Offline traversal-only control: no wire renumbering or production changes.
use super::{cmp_coordinates, rebuild, terms};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{circuit::Circuit, FieldID};
use std::{collections::HashSet, time::Instant};

pub(super) fn analyze<F: AlgebraicField + SerializableField + Clone>(
    f: &F,
    c: &Circuit<F>,
    field_id: FieldID,
) {
    let writer = core_proto::writer::CircuitWriter::new(f, field_id);
    let original = writer.to_bytes_lfc1(c);
    let ks: Vec<_> = c.raw.constants.iter().map(|k| f.to_bytes(k)).collect();
    // Explicit controls, not a per-circuit pick-the-smallest policy.
    let output_major = std::env::var_os("MORTON_LEX_OUTPUT_MAJOR").is_some();
    let orders = if output_major {
        [("lex_g_h0_h1", [0, 1, 2]), ("lex_g_h1_h0", [0, 2, 1])]
    } else {
        [("lex_h1_h0_g", [2, 1, 0]), ("lex_h0_h1_g", [1, 2, 0])]
    };
    for (label, [a0, a1, a2]) in orders {
        let mut ts = terms(c);
        for layer in &mut ts {
            layer.sort_unstable_by(|a, b| {
                (a[a0], a[a1], a[a2])
                    .cmp(&(b[a0], b[a1], b[a2]))
                    .then_with(|| ks[a[3] as usize].cmp(&ks[b[3] as usize]))
            });
        }
        let reordered = rebuild(f, c, ts);
        let mut restored = terms(&reordered);
        for layer in &mut restored {
            layer.sort_unstable_by(|a, b| {
                cmp_coordinates(a, b).then_with(|| ks[a[3] as usize].cmp(&ks[b[3] as usize]))
            });
        }
        assert_eq!(writer.to_bytes_lfc1(&rebuild(f, c, restored)), original);
        let mut unique = HashSet::new();
        for layer in &reordered.raw.layers {
            layer.for_each_delta(|&d| {
                unique.insert(d);
            });
        }
        println!(
            "LEX_CORRECTNESS {label}: canonical_lfc1_exact=true global_deltas={} id={:02x?}",
            unique.len(),
            reordered.id
        );
        super::sizes(&format!("{label}_lfc1"), &writer.to_bytes_lfc1(&reordered));
        super::sizes(
            &format!("{label}_lfc2_native"),
            &writer.to_bytes_lfc2(&reordered),
        );
        let start = Instant::now();
        let segmented = compile_compiler::segment_circuit(f, &reordered);
        println!(
            "LEX_SEGMENT {label}: ms={:.3}",
            start.elapsed().as_secs_f64() * 1000.0
        );
        let bytes = writer.to_bytes_lfc2(&segmented);
        super::sizes(&format!("{label}_lfc2_segmented"), &bytes);
        super::wire_order::memory(label, &segmented);
        let packed = zstd::bulk::compress(&bytes, 16).unwrap();
        let expected = writer.to_bytes_lfc1(&reordered);
        let mut times = Vec::new();
        for _ in 0..3 {
            let start = Instant::now();
            let unpacked = zstd::bulk::decompress(&packed, bytes.len()).unwrap();
            let (decoded, tail) = core_proto::reader::CircuitReader::new(f, field_id)
                .from_bytes_lfc2(&unpacked, true)
                .unwrap();
            times.push(start.elapsed().as_secs_f64() * 1000.0);
            assert!(tail.is_empty());
            assert_eq!(writer.to_bytes_lfc1(&decoded), expected);
        }
        times.sort_by(f64::total_cmp);
        println!(
            "LEX_DECODE {label}: zstd16_decode_and_id_median_ms={:.3} exact=true",
            times[1]
        );
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn input_lexicographic_order_survives_translation() {
        for a0 in 0u32..8 {
            for a1 in 0u32..8 {
                for b0 in 0u32..8 {
                    for b1 in 0u32..8 {
                        assert_eq!(
                            (a1, a0).cmp(&(b1, b0)),
                            (a1 + 7, a0 + 3).cmp(&(b1 + 7, b0 + 3))
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn lexicographic_corners_fold_minor_coordinate_first() {
        // Sparse corners in (h1,h0) order; a coordinate-only version of HQuad's
        // adjacent merge. Every resulting corner must stay unique and sorted.
        let mut corners: Vec<_> = (0u32..8)
            .flat_map(|h1| (0u32..8).map(move |h0| [h0, h1]))
            .filter(|[h0, h1]| (h0 + 3 * h1) % 5 != 0)
            .collect();
        for hand in 0..2 {
            for _ in 0..3 {
                for h in &mut corners {
                    h[hand] >>= 1;
                }
                corners.dedup();
                assert!(corners
                    .windows(2)
                    .all(|p| (p[0][1], p[0][0]) < (p[1][1], p[1][0])));
            }
        }
        assert_eq!(corners, [[0, 0]]);
    }
}
