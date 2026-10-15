// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Trusted-input, offline segmentation experiment; not a production file reader.
//! LCS1 restores the exact original LCT1 bytes, including all maps and metadata.

use super::{get, put, T};
use core_algebra::{AlgebraicField, SerializableField};
use core_proto::{circuit::Circuit, Layer, TermDelta};
use std::{collections::HashMap, time::Instant};

use super::order_sweep::segment_window;

#[derive(Debug, PartialEq, Eq)]
struct Data {
    prefix: Vec<u8>,
    // term count, output count, input count, instance count, map-stream word count
    groups: Vec<[u32; 5]>,
    templates: Vec<T>,
    maps: Vec<[u32; 1]>,
}

fn words(mut input: &[u8]) -> Vec<[u32; 1]> {
    let mut result = Vec::new();
    while !input.is_empty() {
        result.push([get(&mut input)]);
    }
    result
}

fn parse(bytes: &[u8], coefficient_width: usize) -> Data {
    assert_eq!(&bytes[..4], b"LCT1");
    let mut input = &bytes[4..];
    let header: Vec<_> = (0..7).map(|_| get(&mut input)).collect();
    input = &input[header[6] as usize * coefficient_width + 32..];
    for _ in 0..header[5] {
        get(&mut input);
        get(&mut input);
    }
    let prefix = bytes[..bytes.len() - input.len()].to_vec();
    let group_count = get(&mut input);
    let mut data = Data {
        prefix,
        groups: Vec::new(),
        templates: Vec::new(),
        maps: Vec::new(),
    };
    for _ in 0..group_count {
        let nt = get(&mut input);
        let ng = get(&mut input);
        let nh = get(&mut input);
        for _ in 0..nt {
            data.templates
                .push(std::array::from_fn(|_| get(&mut input)));
        }
        let instances = get(&mut input);
        let start = input;
        for instance in 0..instances {
            get(&mut input); // layer difference
            for size in [ng, nh] {
                if instance == 0 {
                    assert_eq!(get(&mut input), size);
                }
                let mut count = 0;
                while count < size {
                    let a = get(&mut input);
                    let b = get(&mut input);
                    let length = if instance == 0 { b } else { a };
                    assert!(length > 0 && length <= size - count);
                    count += length;
                }
            }
        }
        let map_words = words(&start[..start.len() - input.len()]);
        data.groups
            .push([nt, ng, nh, instances, map_words.len().try_into().unwrap()]);
        data.maps.extend(map_words);
    }
    assert!(input.is_empty());
    data
}

fn restore(data: &Data) -> Vec<u8> {
    let mut out = data.prefix.clone();
    put(&mut out, data.groups.len().try_into().unwrap());
    let (mut ti, mut mi) = (0, 0);
    for &[nt, ng, nh, instances, nm] in &data.groups {
        for n in [nt, ng, nh] {
            put(&mut out, n);
        }
        for t in &data.templates[ti..ti + nt as usize] {
            for &n in t {
                put(&mut out, n);
            }
        }
        put(&mut out, instances);
        for &[n] in &data.maps[mi..mi + nm as usize] {
            put(&mut out, n);
        }
        ti += nt as usize;
        mi += nm as usize;
    }
    assert_eq!(ti, data.templates.len());
    assert_eq!(mi, data.maps.len());
    out
}

fn validate_terms<F: SerializableField>(data: &Data, f: &F, c: &Circuit<F>) {
    let mut expected_header = super::header(f, c);
    expected_header[3] = b'1';
    assert_eq!(data.prefix, expected_header);
    let mut actual = vec![Vec::<T>::new(); c.raw.layers.len()];
    let (mut ti, mut mi) = (0, 0);
    for &[nt, ng, nh, instances, nm] in &data.groups {
        let mut local = Vec::new();
        let mut previous = [0u32; 3];
        for t in &data.templates[ti..ti + nt as usize] {
            for j in 0..3 {
                previous[j] = previous[j].wrapping_add(super::unzig(t[j]));
            }
            local.push([previous[0], previous[1], previous[2], t[3]]);
        }
        let mut bytes = Vec::new();
        for &[n] in &data.maps[mi..mi + nm as usize] {
            put(&mut bytes, n);
        }
        let mut input = bytes.as_slice();
        let (mut gs, mut hs, mut depth) = (Vec::new(), Vec::new(), 0usize);
        for instance in 0..instances {
            depth += get(&mut input) as usize;
            if instance == 0 {
                gs = super::get_map(&mut input);
                hs = super::get_map(&mut input);
                assert_eq!(gs.len(), ng as usize);
                assert_eq!(hs.len(), nh as usize);
            } else {
                super::get_map_difference(&mut input, &mut gs);
                super::get_map_difference(&mut input, &mut hs);
            }
            for &[g, local_a, local_b, k] in &local {
                let (a, b) = (hs[local_a as usize], hs[local_b as usize]);
                actual[depth].push([gs[g as usize], a.min(b), a.max(b), k]);
            }
        }
        assert!(input.is_empty());
        ti += nt as usize;
        mi += nm as usize;
    }
    let expected = super::terms(c);
    for (mut a, mut b) in actual.into_iter().zip(expected) {
        a.sort_unstable();
        b.sort_unstable();
        assert_eq!(
            a, b,
            "LCT1 must preserve every absolute term and coefficient"
        );
    }
}

fn plain<const N: usize>(records: &[[u32; N]]) -> Vec<u8> {
    let mut out = vec![0];
    put(&mut out, records.len().try_into().unwrap());
    for record in records {
        for &n in record {
            put(&mut out, n);
        }
    }
    out
}

fn segmented<const N: usize>(records: &[[u32; N]], window: usize) -> [Vec<u8>; 2] {
    // Use the existing experimental LFC2 grouped-literal segmenter on a symbol
    // sequence. These synthetic deltas carry only dictionary IDs, not circuit wires.
    let mut dictionary = Vec::new();
    let mut lookup = HashMap::<[u32; N], u32>::new();
    let sequence: Vec<_> = records
        .iter()
        .map(|&record| {
            *lookup.entry(record).or_insert_with(|| {
                let id = dictionary.len().try_into().unwrap();
                dictionary.push(record);
                id
            })
        })
        .collect();
    let deltas = (0..dictionary.len())
        .map(|i| TermDelta {
            g: i.try_into().unwrap(),
            h: [0, 0],
            k_index: 0,
        })
        .collect();
    let source =
        Layer::<compile_algebra::p256::P256Field>::new(0, 0, deltas, vec![sequence], vec![0]);
    let encoded = segment_window::segment_layer(&source, window);
    let mut out = vec![1];
    put(&mut out, records.len().try_into().unwrap());
    put(&mut out, encoded.deltas().len().try_into().unwrap());
    for delta in encoded.deltas() {
        for &n in &dictionary[delta.g as usize] {
            put(&mut out, n);
        }
    }
    put(&mut out, encoded.delta_segments().len().try_into().unwrap());
    for segment in encoded.delta_segments() {
        put(&mut out, segment.len().try_into().unwrap());
        for &id in segment {
            put(&mut out, id);
        }
    }
    put(&mut out, encoded.delta_tokens().len().try_into().unwrap());
    for &id in encoded.delta_tokens() {
        put(&mut out, id);
    }
    // A second control stores whole raw runs, avoiding the atom dictionary.
    // Keep these runs in first-use order, rather than frequency order, to retain
    // as much original byte locality as possible for outer zstd compression.
    let mut raw = vec![2];
    put(&mut raw, records.len().try_into().unwrap());
    put(&mut raw, encoded.delta_segments().len().try_into().unwrap());
    let mut remap = vec![None; encoded.delta_segments().len()];
    let mut next_id = 0;
    for &id in encoded.delta_tokens() {
        if remap[id as usize].is_some() {
            continue;
        }
        remap[id as usize] = Some(next_id);
        next_id += 1;
        let segment = &encoded.delta_segments()[id as usize];
        put(&mut raw, segment.len().try_into().unwrap());
        for &delta in segment {
            for &n in &dictionary[encoded.deltas()[delta as usize].g as usize] {
                put(&mut raw, n);
            }
        }
    }
    assert_eq!(next_id as usize, encoded.delta_segments().len());
    put(&mut raw, encoded.delta_tokens().len().try_into().unwrap());
    for &id in encoded.delta_tokens() {
        put(&mut raw, remap[id as usize].unwrap());
    }
    [out, raw]
}

fn read_pool<const N: usize>(input: &mut &[u8]) -> Vec<[u32; N]> {
    let mode = get(input);
    let count = get(input) as usize;
    if mode == 0 {
        return (0..count)
            .map(|_| std::array::from_fn(|_| get(input)))
            .collect();
    }
    if mode == 2 {
        let ns = get(input);
        let segments: Vec<Vec<[u32; N]>> = (0..ns)
            .map(|_| {
                let n = get(input);
                (0..n)
                    .map(|_| std::array::from_fn(|_| get(input)))
                    .collect()
            })
            .collect();
        let nt = get(input);
        let mut out = Vec::with_capacity(count);
        for _ in 0..nt {
            let segment = &segments[get(input) as usize];
            assert!(segment.len() <= count - out.len());
            out.extend_from_slice(segment);
        }
        assert_eq!(out.len(), count);
        return out;
    }
    assert_eq!(mode, 1);
    let nd = get(input);
    let dictionary: Vec<[u32; N]> = (0..nd)
        .map(|_| std::array::from_fn(|_| get(input)))
        .collect();
    let ns = get(input);
    let segments: Vec<Vec<u32>> = (0..ns)
        .map(|_| {
            let size = get(input);
            (0..size).map(|_| get(input)).collect()
        })
        .collect();
    let nt = get(input);
    let mut out = Vec::with_capacity(count);
    for _ in 0..nt {
        for &id in &segments[get(input) as usize] {
            assert!(out.len() < count);
            out.push(dictionary[id as usize]);
        }
    }
    assert_eq!(out.len(), count);
    out
}

fn container(data: &Data, templates: &[u8], maps: &[u8]) -> Vec<u8> {
    let mut out = b"LCS1".to_vec();
    put(&mut out, data.prefix.len().try_into().unwrap());
    out.extend(&data.prefix);
    put(&mut out, data.groups.len().try_into().unwrap());
    for group in &data.groups {
        for &n in group {
            put(&mut out, n);
        }
    }
    out.extend(templates);
    out.extend(maps);
    out
}

fn decode(bytes: &[u8]) -> Data {
    assert_eq!(&bytes[..4], b"LCS1");
    let mut input = &bytes[4..];
    let prefix_len = get(&mut input) as usize;
    let prefix = input[..prefix_len].to_vec();
    input = &input[prefix_len..];
    let group_count = get(&mut input);
    let groups = (0..group_count)
        .map(|_| std::array::from_fn(|_| get(&mut input)))
        .collect();
    let templates = read_pool(&mut input);
    let maps = read_pool(&mut input);
    assert!(input.is_empty());
    Data {
        prefix,
        groups,
        templates,
        maps,
    }
}

fn measure(name: &str, policy: &str, bytes: &[u8], original: &[u8], z22: bool) {
    let packed = zstd::bulk::compress(bytes, 16).unwrap();
    let packed22 = z22.then(|| zstd::bulk::compress(bytes, 22).unwrap());
    let mut times = Vec::new();
    for _ in 0..3 {
        let start = Instant::now();
        let unpacked = zstd::bulk::decompress(&packed, bytes.len()).unwrap();
        let recovered = if policy == "lct1" {
            unpacked
        } else {
            restore(&decode(&unpacked))
        };
        times.push(start.elapsed().as_secs_f64() * 1000.);
        assert_eq!(recovered, original);
    }
    times.sort_by(f64::total_cmp);
    println!("LCT_SEG dataset={name} policy={policy} raw={} zstd16={} zstd22={} decode_to_lct1_ms={:.3} exact=true",
        bytes.len(), packed.len(), packed22.map_or(0, |p| p.len()), times[1]);
}

pub fn analyze<F: AlgebraicField + SerializableField + Clone>(name: &str, f: &F, c: &Circuit<F>) {
    let original = {
        let terms = super::terms(c);
        let graph = super::graph(f, c, &terms);
        let blocks = super::blocks(&graph, &terms, false);
        super::encode_grouped(f, c, &blocks)
    };
    let data = parse(&original, f.serialized_size_bytes());
    assert_eq!(restore(&data), original);
    validate_terms(&data, f, c);
    let z22 = std::env::var_os("LCT_ZSTD22").is_some();
    let windows: Vec<usize> = std::env::var("LCT_WINDOWS")
        .unwrap_or_else(|_| "1,4,8,16,32,64,128".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    assert!(windows.iter().all(|w| *w > 0));
    measure(name, "lct1", &original, &original, true);
    let tp = plain(&data.templates);
    let mp = plain(&data.maps);
    println!("LCT_PARTS dataset={name} groups={} template_records={} map_words={} templates_plain={} maps_plain={}",
        data.groups.len(), data.templates.len(), data.maps.len(), tp.len(), mp.len());
    measure(
        name,
        "split_plain",
        &container(&data, &tp, &mp),
        &original,
        true,
    );
    for window in windows {
        let ts = segmented(&data.templates, window);
        let ms = segmented(&data.maps, window);
        for (kind, index) in [("", 0), ("raw_", 1)] {
            println!("LCT_POOLS dataset={name} kind={kind} window={window} templates_segmented={} maps_segmented={}", ts[index].len(), ms[index].len());
            for (scope, t, m) in [
                ("templates", &ts[index], &mp),
                ("maps", &tp, &ms[index]),
                ("both", &ts[index], &ms[index]),
            ] {
                let bytes = container(&data, t, m);
                measure(
                    name,
                    &format!("{kind}{scope}_w{window}"),
                    &bytes,
                    &original,
                    z22,
                );
            }
        }
    }
    assert_eq!(core_proto::circuit::compute_id(f, &c.raw), c.id);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pools_roundtrip_repetitions_tails_and_empty() {
        let mut records: Vec<_> = (0..400)
            .map(|i| [i % 13, (i * 7) % 9, u32::MAX, 0])
            .collect();
        records.extend_from_within(23..300);
        for sample in [&records[..], &records[..1], &records[..0]] {
            for window in [1, 4, 8, 16, 32, 64, 128] {
                for bytes in segmented(sample, window) {
                    let mut input = bytes.as_slice();
                    assert_eq!(read_pool::<4>(&mut input), sample);
                    assert!(input.is_empty());
                }
            }
            let bytes = plain(sample);
            assert_eq!(read_pool::<4>(&mut bytes.as_slice()), sample);
        }
    }
}
