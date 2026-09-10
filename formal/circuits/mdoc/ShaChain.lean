/-
# From per-block compression to the message hash

`meaning` takes `sha256 w.preimage w.nblocks = w.e` as its one remaining hypothesis. That is a
statement about a **seven-block** hash, and every SHA-256 bridge in this tree — the 72 modules of
`quadcert/Bridge/Sha256/` over 𝔽ₚ₂₅₆, and `Bridge/Sha256Gf2/` over GF(2¹²⁸) — proves a statement
about **one** block: eight outgoing chaining words equal `SHA256.blockFrom` of the incoming ones
and the message block.

This file is the gap between them, and it needs no artifact: the circuit's chaining is visible in
`sha256msg::assert_intermediate_hashes`, which is a `for` loop carrying `h` across `MAX_BLOCKS`
`assert_transform_block` calls, and the specification's is `hashBlocks`. Closing it turns
`ShaOfBlocks` from "the whole SHA-256 bridge, at mdoc's block count" into "one `blockFrom` fact
per block" — which is exactly what a per-block bridge delivers.

## What the circuit does

```rust
let mut h = self.initial_context();                     // H0
assert_mapi("assert_intermediate_hashes", 0..MAX_BLOCKS, |b| {
    let tmp = …input_bytes[64b .. 64(b+1)]…;            // big-endian words
    let a = self.sha.assert_transform_block(&Given { input_block: tmp, h0: h.clone() }, &derived[b]);
    h = derived[b].h1.clone();                          // the chaining
    a
})
```

So the assertions give, per block, `derived[b].h1 = blockFrom (b = 0 ? H0 : derived[b-1].h1)
(block b)`. `ChainOk` below is that, verbatim. Note it holds for **all** `MAX_BLOCKS = 40` blocks,
not just the active ones — the circuit compresses the zero padding too and simply does not read
the result.

`assert_final_hash` then muxes on a one-hot selector for `nblocks` and asserts the selected
`h1` is the expected digest. That selection is the one sub-obligation this file leaves standing;
see `## Residual`.

## Why the fuel matters

`blocksOf` is fuel-driven, and its second pattern is `_, [] => []` — it stops early if the word
list runs out. So the induction needs the buffer to actually contain `maxBlocks` blocks, which
for mdoc it does exactly: 2560 bytes is 640 words is 40 blocks. `hbuf` is that hypothesis, and
without it the theorem would be false rather than merely unprovable.
-/

import mdoc.Spec
import mdoc.Assertions

namespace MDoc
namespace ShaChain

/-! ## The circuit's chaining -/

/-- Block `b` of a word list: sixteen words from `16 * b`. -/
def blockAt (ws : List Nat) (b : Nat) : List Nat := (ws.drop (16 * b)).take 16

/-- The accumulator going *into* block `b`: `H0` for the first, the previous block's output
    after that. -/
def chainIn (hOut : Nat → List Nat) (b : Nat) : List Nat :=
  if b = 0 then SHA256.H0 else hOut (b - 1)

/-- **What `assert_intermediate_hashes` asserts**, once the per-block bridge has read it: each
    block's outgoing chaining words are `blockFrom` of the incoming ones and that block. -/
def ChainOk (ws : List Nat) (maxBlocks : Nat) (hOut : Nat → List Nat) : Prop :=
  ∀ b, b < maxBlocks → hOut b = SHA256.blockFrom (chainIn hOut b) (blockAt ws b)

/-! ## The induction

Generalised over the starting block, because the accumulator changes as the fold walks. -/

private theorem drop_step (ws : List Nat) (j : Nat) :
    (ws.drop (16 * j)).drop 16 = ws.drop (16 * (j + 1)) := by
  rw [List.drop_drop, show 16 * j + 16 = 16 * (j + 1) by omega]

/-- Folding `blocksOf` from block `j` reproduces the chain. -/
theorem hashBlocks_chain (ws : List Nat) (maxBlocks : Nat) (hOut : Nat → List Nat)
    (hbuf : 16 * maxBlocks ≤ ws.length) (hch : ChainOk ws maxBlocks hOut) :
    ∀ (n j : Nat), 0 < n → j + n ≤ maxBlocks →
      hashBlocks (chainIn hOut j) (blocksOf n (ws.drop (16 * j))) = hOut (j + n - 1) := by
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ m ih =>
      intro j _ hjm
      -- the remaining words are non-empty, so `blocksOf` takes its cons branch
      obtain ⟨x, xs, hx⟩ : ∃ x xs, ws.drop (16 * j) = x :: xs := by
        rcases hd : ws.drop (16 * j) with _ | ⟨x, xs⟩
        · exfalso
          have hz : (ws.drop (16 * j)).length = 0 := by rw [hd]; rfl
          rw [List.length_drop] at hz
          have : 16 * j + 16 ≤ 16 * maxBlocks := by omega
          omega
        · exact ⟨x, xs, rfl⟩
      have hstep : blocksOf (m + 1) (ws.drop (16 * j))
          = blockAt ws j :: blocksOf m ((ws.drop (16 * j)).drop 16) := by
        show blocksOf (m + 1) (ws.drop (16 * j))
          = (ws.drop (16 * j)).take 16 :: blocksOf m ((ws.drop (16 * j)).drop 16)
        rw [hx]; rfl
      rw [hstep, drop_step]
      show hashBlocks (SHA256.blockFrom (chainIn hOut j) (blockAt ws j))
        (blocksOf m (ws.drop (16 * (j + 1)))) = hOut (j + (m + 1) - 1)
      rw [← hch j (by omega)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · show hashBlocks (hOut j) [] = hOut (j + (0 + 1) - 1)
        show hOut j = hOut (j + (0 + 1) - 1)
        congr 1
      · have hnext : chainIn hOut (j + 1) = hOut j := by
          simp only [chainIn]
          rw [if_neg (by omega)]
          congr 1
        rw [← hnext, ih (j + 1) hm (by omega)]
        congr 1
        omega

/-- **The chaining, discharged.** Per-block `blockFrom` facts plus the selected digest give the
    hypothesis `meaning` asks for. -/
theorem sha256_of_chain (buf : List Nat) (maxBlocks nblocks : Nat) (hOut : Nat → List Nat)
    (digest : List Nat)
    (hbuf : 16 * maxBlocks ≤ (wordsOfBytes buf).length)
    (hch : ChainOk (wordsOfBytes buf) maxBlocks hOut)
    (hn : 0 < nblocks) (hnm : nblocks ≤ maxBlocks)
    (hsel : bytesOfWords (hOut (nblocks - 1)) = digest) :
    sha256 buf nblocks = digest := by
  have h := hashBlocks_chain (wordsOfBytes buf) maxBlocks hOut hbuf hch nblocks 0 hn (by omega)
  simp only [chainIn, Nat.mul_zero, List.drop_zero, Nat.zero_add, if_pos] at h
  simp only [sha256, h, hsel]

/-! ## The buffer really does hold `maxBlocks` blocks

`hbuf` is a fact about the padded buffer's length, and for the two mdoc instances it is exact. -/

/-- Four bytes make a word. -/
theorem wordsOfBytes_length : ∀ bs : List Nat, (wordsOfBytes bs).length = bs.length / 4
  | [] => rfl
  | [_] => by simp [wordsOfBytes]
  | [_, _] => by simp [wordsOfBytes]
  | [_, _, _] => by simp [wordsOfBytes]
  | a :: b :: c :: d :: rest => by
      have ih := wordsOfBytes_length rest
      simp only [wordsOfBytes, List.length_cons, ih]
      omega

/-- The MSO buffer: 2560 bytes, 640 words, 40 blocks — exactly. -/
theorem mso_buf_fits (buf : List Nat) (h : buf.length = maxShaBlocks * 64) :
    16 * maxShaBlocks ≤ (wordsOfBytes buf).length := by
  rw [wordsOfBytes_length, h]; simp only [maxShaBlocks]; omega

/-- An attribute's buffer: 128 bytes, 32 words, 2 blocks. -/
theorem attr_buf_fits (buf : List Nat) (h : buf.length = attrShaBlocks * 64) :
    16 * attrShaBlocks ≤ (wordsOfBytes buf).length := by
  rw [wordsOfBytes_length, h]; simp only [attrShaBlocks]; omega

/-! ## The reduced meaning theorem -/

/-- **`meaning`, with its SHA hypothesis replaced by per-block facts.** The MSO's forty blocks and
    each attribute's two, each as one `blockFrom` equation, plus the digest each chain lands on.
    This is the shape a per-block bridge delivers, so it is where `Bridge/Sha256Gf2/` will
    plug in.

    `0 < nblocks ≤ maxShaBlocks` is not a hypothesis: it comes out of `assert_nblocks`, which is
    already in `Asserted`. -/
theorem meaning_of_blocks (g : Gadgets) (s : Statement) (w : Witness)
    (hOut : Nat → List Nat) (hOutA : Nat → Nat → List Nat)
    (hg : GadgetsOk g) (hwd : Widths s w) (hwf : WellFormed s)
    -- the MSO's chain
    (hlen : w.preimage.length = maxShaBlocks * 64)
    (hch : ChainOk (wordsOfBytes w.preimage) maxShaBlocks hOut)
    (hsel : bytesOfWords (hOut (w.nblocks - 1)) = w.e)
    -- and each attribute's
    (hlenA : ∀ i, i < s.attrId.length →
      (w.attrs.getD i default).preimage.length = attrShaBlocks * 64)
    (hchA : ∀ i, i < s.attrId.length →
      ChainOk (wordsOfBytes (w.attrs.getD i default).preimage) attrShaBlocks (hOutA i))
    (hselA : ∀ i, i < s.attrId.length →
      bytesOfWords (hOutA i (attrShaBlocks - 1))
        = window w.preimage ((w.attrs.getD i default).digestOff + tag32.length) 32)
    (h : Asserted g s w) :
    ValidPresentation s := by
  have hsp : ShaPadded maxShaBlocks w.preimage w.msgLen w.nblocks := by
    have p40 : (2 : Nat) ^ nblocksBits = 1099511627776 := rfl
    have p16 : (2 : Nat) ^ hashIndexBits = 65536 := rfl
    have h32 : (2 : Nat) ^ 32 = 4294967296 := rfl
    have hn := hwd.nblocks
    have hm := hwd.msgLen
    rw [p16] at hm
    exact shaPadded_of_asserted hg (by rw [p40]; omega) (by rw [p40, maxShaBlocks]; omega)
      (by rw [h32]; omega) h.1
  refine meaning g s w hg hwd hwf ?_ ?_ h
  · exact sha256_of_chain w.preimage maxShaBlocks w.nblocks hOut w.e
      (mso_buf_fits w.preimage hlen) hch hsp.1 hsp.2.1 hsel
  · intro i hi
    exact sha256_of_chain _ attrShaBlocks attrShaBlocks (hOutA i) _
      (attr_buf_fits _ (hlenA i hi)) (hchA i hi) (by simp [attrShaBlocks])
      (by omega) (hselA i hi)

/-! ## Residual

What is left of `ShaOfBlocks` after this file and `mdoc/Mux.lean`, and where each piece goes.

* **The per-block compression** — still open. `hOut b = blockFrom (chainIn hOut b) (blockAt ws b)`,
  forty times for the MSO and twice per attribute. This is exactly what `Bridge/Sha256/`'s
  `sha256_block_of_bytes` states for 𝔽ₚ₂₅₆ and what `Bridge/Sha256Gf2/` is being built to state
  for GF(2¹²⁸) — but for *those* artifacts. Applying it to mdoc needs the mdoc circuit ingested,
  which is steps 1-3 and not started. This is now the only open piece.

* **The final one-hot selection** — closed by `Mux.oneHotSum_select` and `oneHotSum_select_vec`.
  `assert_final_hash` builds `selector[b] = eqb(nblocks, b + 1)` and runs 8 × 32 muxes off that one
  selector; the sum is block `nblocks - 1`'s wires verbatim.

* **The byte order** — closed by `Mux.regOf_index`, which states `mm_bits[(7 - j) * 32 + k] =
  x[j][k]` as a theorem, and `Mux.bval_regOf`, which gives the register's value as the words read
  most-significant-word-first. `GoldenCheck.sha256_empty` and `Golden.shaMso` remain as independent
  checks of the same convention on real bytes.

`Mux.hsel_of_final_hash` composes those two and concludes `bytesOfWords (hOut (n - 1)) = e`, which
is `meaning_of_blocks`'s `hsel` verbatim — so `hsel` is a hypothesis here only because this module
stays Mathlib-free (`Golden.chain_digest`'s `decide +kernel` would pay for the import).

The reduction is the point: `meaning`'s SHA hypothesis was one opaque statement about a 403-byte
message. It is now forty per-block statements of exactly the shape the existing bridges prove.
-/

end ShaChain
end MDoc
