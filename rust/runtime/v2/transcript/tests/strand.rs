// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::*;

// Replay helpers are test-only and do not grant production callers snapshots.
impl Strand {
    pub(in crate::runtime::v2) fn clone_for_test(&self) -> Self {
        Self {
            hash: self.hash.clone(),
            id: self.id,
        }
    }
}

fn root(message: &[u8]) -> Strand {
    let mut strand = Strand::new();
    strand.write(message);
    strand
}

fn output(mut strand: Strand, message: &[u8]) -> String {
    strand.write(message);
    hex::encode(strand.end_strand().next_block())
}

#[test]
fn independent_root_and_prf_vectors() {
    // Generated independently with Python hashlib and struct '<I'/'<Q'.
    let mut prf = root(b"root").end_strand();
    for expected in [
        "2bd42698e06f013ba2af6a3138d6d9429bd5b3ea5f47c9c6a0a320ce645aa498",
        "daf6cf6aed4af61d4d636f2557dda2ce0cdcc3e055c704658ff6e4dfd2cbe3e6",
        "b42937243d1c5754475dea046c55463a5537b4ba3babf68f582bf1b34a04d399",
    ] {
        assert_eq!(hex::encode(prf.next_block()), expected);
    }
    assert_eq!(
        hex::encode(root(b"").end_strand().next_block()),
        "9315e3b589b63494be56ad53e9a946179fd8d67b6d0d54ec19bdb66d38d70cc4"
    );
}

#[test]
fn independent_continuation_vectors() {
    let (mut prf, mut next) = root(b"root").continue_strand();
    assert_eq!(
        hex::encode(prf.next_block()),
        "2bd42698e06f013ba2af6a3138d6d9429bd5b3ea5f47c9c6a0a320ce645aa498"
    );
    next.write(b"child");
    let (mut child_prf, last) = next.continue_strand();
    assert_eq!(
        hex::encode(child_prf.next_block()),
        "1749816695211f4e755d9b4d1f70b73655095b40ed90ea1412e34a4ca3c98933"
    );
    assert_eq!(
        output(last, b"next"),
        "7d58ecd69b508ce863f7bc8ba236e10bb6492d70d113d9dbe05c65f269624e9e"
    );
}

#[test]
fn node_ids_bind_positions_even_with_identical_parents_and_messages() {
    let parent = [0x5a; BLOCK_BYTES];
    for (id, expected) in [
        (
            1,
            "dc202fd39c7135f799b0f402a9a02c4a5260295f7f860f2d4754843c4a0935e7",
        ),
        (
            2,
            "00c315386fe8a1409fbf030501bcd8a74d82bb81ed08c451b81daecc6a51d46c",
        ),
        (
            0x0102030405060708,
            "8984e362be7efbb211a019c450c7899be5805a241ea830ce4f87b726e6539dac",
        ),
    ] {
        assert_eq!(
            output(Strand::with_parent(id, Some(&parent)), b"message"),
            expected
        );
    }
}

#[test]
fn prf_ids_bind_positions_even_with_colliding_node_digests() {
    for (id, expected) in [
        (
            1,
            "6985dd30994c62d553670e1424d365c81abe5a932d71d4900c3e2e6800b7cc0b",
        ),
        (
            2,
            "02e9823433a3972f5d195cb875058f7893e373100f4be2c00271a9e4be9ebbc4",
        ),
    ] {
        let mut prf = Prf {
            id,
            parent: [0x5a; BLOCK_BYTES],
            counter: 0,
        };
        assert_eq!(hex::encode(prf.next_block()), expected);
    }
}

#[test]
fn ids_increase_once_per_continuation() {
    let mut strand = Strand::new();
    for expected in 0..32 {
        assert_eq!(strand.id, expected);
        let (prf, next) = strand.continue_strand();
        assert_eq!(prf.id, expected);
        assert_eq!(next.id, expected + 1);
        strand = next;
    }
}

#[test]
fn last_strand_id_can_be_finalized() {
    let strand = Strand::with_parent(u64::MAX - 1, Some(&[0; BLOCK_BYTES]));
    let (_, last) = strand.continue_strand();
    assert_eq!(last.id, u64::MAX);
    let mut prf = last.end_strand();
    assert_eq!(prf.id, u64::MAX);
    prf.next_block();
}

#[test]
#[should_panic(expected = "strand id exhausted")]
fn strand_id_does_not_wrap() {
    let strand = Strand::with_parent(u64::MAX, Some(&[0; BLOCK_BYTES]));
    let _ = strand.continue_strand();
}

#[test]
fn caught_id_overflow_cannot_restart_the_chain() {
    let mut strand = Strand::with_parent(u64::MAX, Some(&[0; BLOCK_BYTES]));
    strand.write(b"terminal");
    let expected = strand.clone_for_test().end_strand().next_block();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        strand.continue_in_place()
    }))
    .is_err());
    assert_eq!(strand.id, u64::MAX);
    assert_eq!(strand.end_strand().next_block(), expected);
}

#[test]
fn writes_are_raw_stream_fragments() {
    let mut strand = Strand::new();
    strand.write(b"ro");
    strand.write(b"");
    strand.write(b"ot");
    assert_eq!(
        strand.end_strand().next_block(),
        root(b"root").end_strand().next_block()
    );
}

#[test]
fn continuation_is_independent_of_prf_reads() {
    let (mut prf, next) = root(b"independent").continue_strand();
    let (mut reference, ref_next) = root(b"independent").continue_strand();
    assert_eq!(prf.next_block(), reference.next_block());
    for _ in 0..8 {
        prf.next_block();
    }
    assert_eq!(output(next, b"body"), output(ref_next, b"body"));
}

#[test]
fn empty_continuations_are_reproducible_and_distinct() {
    let (mut first_prf, second) = root(b"empty chain").continue_strand();
    let (mut second_prf, third) = second.continue_strand();
    let first = first_prf.next_block();
    let second_output = second_prf.next_block();
    let third_output = third.end_strand().next_block();
    assert_ne!(first, second_output);
    assert_ne!(first, third_output);
    assert_ne!(second_output, third_output);
    let (mut replay, _) = root(b"empty chain").continue_strand();
    assert_eq!(first, replay.next_block());
}

#[test]
fn reader_preserves_block_tails_and_does_not_query_for_empty_reads() {
    let mut reader = Reader::new(root(b"stream").end_strand());
    reader.read(&mut []);
    assert_eq!(reader.prf.counter, 0);
    let mut actual = Vec::new();
    for n in [1, 0, 30, 1, 1, 32, 127, 65537] {
        let mut part = vec![0; n];
        reader.read(&mut part);
        actual.extend_from_slice(&part);
    }
    let mut reference = root(b"stream").end_strand();
    let expected: Vec<_> = (0..actual.len().div_ceil(BLOCK_BYTES))
        .flat_map(|_| reference.next_block())
        .take(actual.len())
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(
        reader.prf.counter as usize,
        actual.len().div_ceil(BLOCK_BYTES)
    );
}

#[test]
#[should_panic(expected = "strand PRF counter exhausted")]
fn prf_counter_does_not_wrap() {
    let mut prf = root(b"overflow").end_strand();
    prf.counter = u64::MAX - 1;
    prf.next_block();
    assert_eq!(prf.counter, u64::MAX);
    prf.next_block();
}
