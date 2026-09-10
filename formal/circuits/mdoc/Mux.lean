/-
# `assert_final_hash`'s one-hot selection

The second of the two things `ShaChain` left standing in `ShaOfBlocks`. `sha256msg`'s last step
is

```rust
for b in 0..MAX_BLOCKS { selector.push(self.bv.eqb(nblocks, &self.bv.of_u64((b + 1) as u64))); }
for i in 0..8 { x.push(self.bv.one_hot_mux(&selector, &|b| derived[b].h1[i].clone())); }
// mm_bits[(7 - j) * 32 + k] = x[j][k];  assert_eq("hash_eq", &mm, expected_hash)
```

`one_hot_muxb` is `sum_assuming_at_most_one_true` over `selector[b] · data(b)` — a plain field
sum, sound because the selector is one-hot. So the output is the chaining words of block
`nblocks - 1`, and `ShaChain.sha256_of_chain`'s `hsel` is what that gives.

## A correction

I recorded last session that the comparator and chunked-equality lemmas could not be threaded
into `meaning` because their conclusions are about bit lists while `Asserted` is about bytes, and
that closing the gap would mean carrying bit decompositions in `Witness`. That was wrong, and this
file is where it shows: the bit decomposition of a byte is a **function** of the byte, not extra
data. `toBits` is that function, and `toBits_bval` says a boolean wire vector is determined by its
value — so no witness data is added, and the "bit-packing convention" is a lemma rather than an
assumption.

It is still true that threading `Compare` and `ChunkEq` is a refactor of `Asserted`; what is not
true is that it needs new witness fields.

## What this file does not close

The per-block compression itself — `hOut b = blockFrom (chainIn hOut b) (blockAt ws b)`, which is
what `Bridge/Sha256Gf2/` proves for its own artifact. Applying it to mdoc needs the mdoc circuit
ingested, which is steps 1-3 and a different track. After this file that is the *only* piece of
`ShaOfBlocks` left.

`hsel_of_final_hash` is the end of the chain here: it takes the muxes, the selector's one-hotness
and `assert_eq`, and concludes `bytesOfWords (hOut (n - 1)) = e` — `ShaChain.meaning_of_blocks`'s
`hsel`, verbatim. `ShaChain` does not import this module because it must stay Mathlib-free for
`GoldenChain`'s `decide +kernel`; the composition is by hand at the call site.
-/

import Mathlib
import mdoc.Spec
import mdoc.Compare
import ECDSA.BitLt

set_option maxRecDepth 4000

namespace MDoc
namespace Mux

open ECDSA2.BitLt

/-! ## Bit packing

The convention every clause needs, and it is a round trip rather than a hypothesis. -/

/-- A number's low `w` bits, least significant first — the order `Bitvec` uses. -/
def toBits : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: toBits w (v / 2)

@[simp] theorem toBits_length : ∀ w v, (toBits w v).length = w
  | 0, _ => rfl
  | w + 1, v => by simp [toBits, toBits_length w (v / 2)]

/-- Packing a number below `2 ^ w` into `w` bits recovers it. -/
theorem bval_toBits : ∀ w v, v < 2 ^ w → bval (toBits w v) = v
  | 0, v, h => by simp only [toBits, bval]; simp at h; omega
  | w + 1, v, h => by
      have hv : v / 2 < 2 ^ w := by
        have : (2 : Nat) ^ (w + 1) = 2 * 2 ^ w := by ring
        omega
      have ih := bval_toBits w (v / 2) hv
      simp only [toBits, bval, ih]
      by_cases h2 : v % 2 = 1
      · simp only [h2, decide_true, if_pos]; omega
      · simp only [show (decide (v % 2 = 1)) = false by simp [h2]]; simp; omega

/-- **A boolean wire vector is determined by its value.** This is what makes modelling the byte,
    rather than its eight wires, faithful: `is_boolean` says the wires are bits, and then the byte
    fixes them. -/
theorem toBits_bval : ∀ l : List Bool, toBits l.length (bval l) = l
  | [] => rfl
  | x :: xs => by
      have ih := toBits_bval xs
      simp only [List.length_cons, toBits]
      cases x with
      | false =>
          have h1 : bval (false :: xs) = 2 * bval xs := by simp [bval]
          have h2 : (2 * bval xs) % 2 = 0 := by omega
          have h3 : (2 * bval xs) / 2 = bval xs := by omega
          rw [h1, h2, h3, ih]
          simp
      | true =>
          have h1 : bval (true :: xs) = 1 + 2 * bval xs := by simp [bval]
          have h2 : (1 + 2 * bval xs) % 2 = 1 := by omega
          have h3 : (1 + 2 * bval xs) / 2 = bval xs := by omega
          rw [h1, h2, h3, ih]
          simp

/-- Eight bits per byte, for the byte layer. -/
theorem bval_toBits_byte (v : Nat) (h : v < 256) : bval (toBits 8 v) = v :=
  bval_toBits 8 v (by omega)

/-! ## The one-hot sum

`sum_assuming_at_most_one_true` is a plain field sum; the selector is what makes it a selection. -/

variable {F : Type*} [CommRing F]

/-- `one_hot_muxb selector data`: the circuit builds a `Vec` of `selector[b] · data(b)` and sums
    it, which is this. -/
def oneHotSum (m : Nat) (sel d : Nat → F) : F := ∑ b ∈ Finset.range m, sel b * d b

/-- **The mux selects.** With a one-hot selector at `n - 1`, the sum is that entry — which is what
    makes `sum_assuming_at_most_one_true` sound and what `assert_final_hash` relies on. -/
theorem oneHotSum_select (m n : Nat) (sel d : Nat → F) (hn : 0 < n) (hnm : n ≤ m)
    (hsel : ∀ b, b < m → sel b = if n = b + 1 then 1 else 0) :
    oneHotSum m sel d = d (n - 1) := by
  rw [oneHotSum, Finset.sum_eq_single_of_mem (n - 1) (Finset.mem_range.mpr (by omega))]
  · rw [hsel (n - 1) (by omega), if_pos (by omega), one_mul]
  · intro b hb hne
    rw [hsel b (Finset.mem_range.mp hb), if_neg (by omega), zero_mul]

/-- **One selector, many muxes.** `assert_final_hash` runs 8 × 32 muxes off the *same* `selector`,
    so the whole 256-bit vector comes from one block. This is that, componentwise. -/
theorem oneHotSum_select_vec (m n len : Nat) (sel : Nat → F) (d : Nat → Nat → F)
    (hn : 0 < n) (hnm : n ≤ m) (hsel : ∀ b, b < m → sel b = if n = b + 1 then 1 else 0) :
    (List.range len).map (fun k => oneHotSum m sel (fun b => d b k))
      = (List.range len).map (d (n - 1)) :=
  List.map_congr_left fun k _ => oneHotSum_select m n sel (fun b => d b k) hn hnm hsel

/-! ## The byte order

`mm_bits[(7 - j) * 32 + k] = x[j][k]` puts word 0 highest, which is what `bytesOfWords` writes. -/

private theorem beVal_append (a b : List Nat) :
    beVal (a ++ b) = beVal a * 256 ^ b.length + beVal b := by
  have hfold : ∀ (l : List Nat) (s : Nat),
      l.foldl (fun acc d => acc * 256 + d) s
        = s * 256 ^ l.length + l.foldl (fun acc d => acc * 256 + d) 0 := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons d ds ih =>
        intro s
        have h1 := ih (s * 256 + d)
        have h2 := ih d
        simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
        rw [h1, h2]; ring
  simp only [beVal, List.foldl_append]
  exact hfold b _

theorem bytesOfWords_length : ∀ ws : List Nat, (bytesOfWords ws).length = 4 * ws.length
  | [] => rfl
  | w :: ws => by
      have ih := bytesOfWords_length ws
      simp only [bytesOfWords, List.length_cons, ih]
      ring

/-- The big-endian value of a word list, 32 bits per word — what the 256-bit register holds. -/
def weVal (ws : List Nat) : Nat := ws.foldl (fun acc w => acc * 2 ^ 32 + w) 0

/-- **The unpacking is big-endian over words.** `assert_final_hash` writes word `j` at bit
    positions `(7 - j) * 32 …`, so the 256-bit register it compares is the words read
    most-significant-first — which is `beVal ∘ bytesOfWords`. -/
theorem beVal_bytesOfWords : ∀ ws : List Nat, (∀ w ∈ ws, w < 2 ^ 32) →
    beVal (bytesOfWords ws) = weVal ws
  | [], _ => rfl
  | w :: ws, hall => by
      have hw : w < 2 ^ 32 := hall w (by simp)
      have hrest : ∀ u ∈ ws, u < 2 ^ 32 := fun u hu => hall u (by simp [hu])
      have ih := beVal_bytesOfWords ws hrest
      have hfold : ∀ (l : List Nat) (s : Nat),
          l.foldl (fun acc u => acc * 2 ^ 32 + u) s
            = s * (2 ^ 32) ^ l.length + l.foldl (fun acc u => acc * 2 ^ 32 + u) 0 := by
        intro l
        induction l with
        | nil => intro s; simp
        | cons u us ihu =>
            intro s
            have h1 := ihu (s * 2 ^ 32 + u)
            have h2 := ihu u
            simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
            rw [h1, h2]; ring
      have hsplit : bytesOfWords (w :: ws)
          = [w / 2 ^ 24 % 256, w / 2 ^ 16 % 256, w / 2 ^ 8 % 256, w % 256] ++ bytesOfWords ws :=
        rfl
      rw [hsplit, beVal_append, ih, bytesOfWords_length]
      have hhead : beVal [w / 2 ^ 24 % 256, w / 2 ^ 16 % 256, w / 2 ^ 8 % 256, w % 256] = w := by
        simp only [beVal, List.foldl_cons, List.foldl_nil]
        omega
      rw [hhead]
      simp only [weVal, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
      rw [hfold ws w]
      have hpow : (256 : Nat) ^ (4 * ws.length) = (2 ^ 32) ^ ws.length := by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [hpow]

/-! ## The 256-bit register

`assert_final_hash` finishes with

```rust
for j in 0..8 { for k in 0..32 { mm_bits[(7 - j) * 32 + k] = x[j][k].clone(); } }
self.bv.assert_eq("hash_eq", &mm, expected_hash);
```

Index 0 of a `Bitvec` is the least significant bit, so `j = 0` lands at bit positions 224…255 —
the *top* 32 bits. The register is therefore the eight chaining words read
most-significant-word-first, which is the order `bytesOfWords` transcribes. -/

/-- The register the circuit builds: each word's 32 bits, least significant first, with the
    *last* word lowest. -/
def regOf (ws : List Nat) : List Bool := (ws.reverse.map (toBits 32)).flatten

@[simp] theorem regOf_length (ws : List Nat) : (regOf ws).length = 32 * ws.length := by
  have h : ∀ l : List Nat, (l.map (fun x => (toBits 32 x).length)).sum = 32 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons u us ih =>
        rw [List.map_cons, List.sum_cons, ih, toBits_length, List.length_cons]; ring
  simp only [regOf, List.length_flatten, List.map_map, Function.comp_def, h, List.length_reverse]

private theorem getD_flatten_map (f : Nat → List Bool) (n : Nat) (hf : ∀ x, (f x).length = n) :
    ∀ (l : List Nat) (q r : Nat), q < l.length → r < n →
      ((l.map f).flatten).getD (n * q + r) false = (f (l.getD q 0)).getD r false
  | [], q, r, hq, _ => absurd hq (by simp)
  | x :: xs, 0, r, _, hr => by
      simp only [List.map_cons, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      exact List.getD_append _ _ _ _ (by rw [hf]; exact hr)
  | x :: xs, q + 1, r, hq, hr => by
      have hexp : n * (q + 1) + r = n * q + n + r := by ring
      have ih := getD_flatten_map f n hf xs q r (by simp only [List.length_cons] at hq; omega) hr
      simp only [List.map_cons, List.flatten_cons, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
        show n * (q + 1) + r - n = n * q + r by omega]
      exact ih

/-- **The layout is `mm_bits[(7 - j) * 32 + k] = x[j][k]`.** Reading the register of an eight-word
    list at position `(7 - j) * 32 + k` gives bit `k` of word `j` — the Rust line, as a theorem
    about `regOf`. -/
theorem regOf_index (ws : List Nat) (hlen : ws.length = 8) (j k : Nat) (hj : j < 8) (hk : k < 32) :
    (regOf ws).getD ((7 - j) * 32 + k) false = (toBits 32 (ws.getD j 0)).getD k false := by
  have h1 : 7 - j < ws.reverse.length := by rw [List.length_reverse, hlen]; omega
  have h2 : j < ws.length := by omega
  have hrev : ws.reverse.getD (7 - j) 0 = ws.getD j 0 := by
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_reverse]
    congr 1
    omega
  rw [show (7 - j) * 32 + k = 32 * (7 - j) + k by ring, regOf,
    getD_flatten_map (toBits 32) 32 (toBits_length 32) ws.reverse (7 - j) k h1 hk, hrev]

private theorem weVal_cons (w : Nat) (ws : List Nat) :
    weVal (w :: ws) = w * (2 ^ 32) ^ ws.length + weVal ws := by
  have hfold : ∀ (l : List Nat) (s : Nat),
      l.foldl (fun acc u => acc * 2 ^ 32 + u) s
        = s * (2 ^ 32) ^ l.length + l.foldl (fun acc u => acc * 2 ^ 32 + u) 0 := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons u us ihu =>
        intro s
        have h1 := ihu (s * 2 ^ 32 + u)
        have h2 := ihu u
        simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
        rw [h1, h2]; ring
  simp only [weVal, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  exact hfold ws w

/-- **The register's value is the words, big-endian.** -/
theorem bval_regOf : ∀ ws : List Nat, (∀ w ∈ ws, w < 2 ^ 32) → bval (regOf ws) = weVal ws
  | [], _ => rfl
  | w :: ws, hall => by
      have hw : w < 2 ^ 32 := hall w (by simp)
      have ih := bval_regOf ws (fun u hu => hall u (by simp [hu]))
      have hsplit : regOf (w :: ws) = regOf ws ++ toBits 32 w := by
        simp [regOf, List.reverse_cons]
      rw [hsplit, MDoc.Compare.bval_append, ih, regOf_length, bval_toBits 32 w hw, weVal_cons]
      rw [show (2 : Nat) ^ (32 * ws.length) = (2 ^ 32) ^ ws.length by rw [pow_mul]]
      ring

/-! ## Comparing against the expected digest

`assert_eq` gives bit-for-bit equality with the public digest's `Bitvec`. Turning that into the
byte-list equality `ShaChain.meaning_of_blocks` asks for needs the value map to be injective, which
it is at these lengths. -/

/-- The public digest as the circuit's `Bitvec`. -/
def digestBits (e : List Nat) : List Bool := toBits (8 * e.length) (beVal e)

private theorem beVal_lt : ∀ bs : List Nat, (∀ x ∈ bs, x < 256) → beVal bs < 256 ^ bs.length
  | [], _ => by simp [beVal]
  | b :: bs, h => by
      have hb : b < 256 := h b (by simp)
      have ih := beVal_lt bs (fun x hx => h x (by simp [hx]))
      rw [MDoc.Compare.beVal_cons, List.length_cons, pow_succ]
      have h3 : (b + 1) * 256 ^ bs.length ≤ 256 * 256 ^ bs.length :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : b * 256 ^ bs.length + 256 ^ bs.length = (b + 1) * 256 ^ bs.length := by ring
      omega

theorem bval_digestBits (e : List Nat) (h : ∀ x ∈ e, x < 256) : bval (digestBits e) = beVal e := by
  refine bval_toBits _ _ (lt_of_lt_of_le (beVal_lt e h) (le_of_eq ?_))
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul]

/-- `beVal` is injective on byte strings of a fixed length — the standard positional argument. -/
theorem beVal_inj : ∀ a b : List Nat, a.length = b.length →
    (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) → beVal a = beVal b → a = b
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hlen, ha, hb, hv => by
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hxs := beVal_lt xs (fun u hu => ha u (by simp [hu]))
      have hys := beVal_lt ys (fun u hu => hb u (by simp [hu]))
      rw [hlen'] at hxs
      rw [MDoc.Compare.beVal_cons, MDoc.Compare.beVal_cons, hlen'] at hv
      have hxy : x = y := by
        rcases lt_trichotomy x y with h | h | h
        · exfalso
          have : (x + 1) * 256 ^ ys.length ≤ y * 256 ^ ys.length :=
            Nat.mul_le_mul_right _ (by omega)
          have hexp : (x + 1) * 256 ^ ys.length = x * 256 ^ ys.length + 256 ^ ys.length := by ring
          omega
        · exact h
        · exfalso
          have : (y + 1) * 256 ^ ys.length ≤ x * 256 ^ ys.length :=
            Nat.mul_le_mul_right _ (by omega)
          have hexp : (y + 1) * 256 ^ ys.length = y * 256 ^ ys.length + 256 ^ ys.length := by ring
          omega
      subst hxy
      have hrest : beVal xs = beVal ys := by omega
      rw [beVal_inj xs ys hlen' (fun u hu => ha u (by simp [hu]))
        (fun u hu => hb u (by simp [hu])) hrest]

/-- Every byte `bytesOfWords` writes is a byte. -/
theorem bytesOfWords_lt : ∀ ws : List Nat, ∀ x ∈ bytesOfWords ws, x < 256
  | [], x, hx => by simp [bytesOfWords] at hx
  | u :: us, x, hx => by
      have ih := bytesOfWords_lt us
      have hx' : x ∈ [u / 2 ^ 24 % 256, u / 2 ^ 16 % 256, u / 2 ^ 8 % 256, u % 256]
          ++ bytesOfWords us := hx
      rcases List.mem_append.mp hx' with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> omega
      · exact ih x h

/-- **`ShaChain`'s `hsel`, from the circuit's comparison.** If the register the muxes fill equals
    the expected digest's bit vector, then the selected block's chaining words, unpacked
    big-endian, *are* that digest — which is exactly the hypothesis `meaning_of_blocks` takes. -/
theorem bytesOfWords_of_regOf (hw e : List Nat) (hlen : hw.length = 8) (helen : e.length = 32)
    (hwb : ∀ u ∈ hw, u < 2 ^ 32) (heb : ∀ x ∈ e, x < 256)
    (hreg : regOf hw = digestBits e) : bytesOfWords hw = e := by
  have hval : weVal hw = beVal e := by
    rw [← bval_regOf hw hwb, hreg, bval_digestBits e heb]
  refine beVal_inj _ _ (by rw [bytesOfWords_length, hlen, helen]) (bytesOfWords_lt hw) heb ?_
  rw [beVal_bytesOfWords hw hwb, hval]

/-! ## `assert_final_hash`, end to end

The muxes fill the register from one block; `assert_eq` pins the register to the public digest.
Composing them lands exactly on `ShaChain.meaning_of_blocks`'s `hsel`. -/

/-- The field element a wire carries once `is_boolean` has pinned it. -/
def emb (b : Bool) : F := if b then 1 else 0

theorem emb_inj [Nontrivial F] : Function.Injective (emb : Bool → F) := by
  intro a b hab
  cases a <;> cases b <;> simp only [emb, if_true, if_false] at hab ⊢
  · exact absurd hab.symm one_ne_zero
  · exact absurd hab one_ne_zero

/-- **`assert_final_hash` gives `ShaChain`'s `hsel`.** `hmux` is the 256 muxes (one shared
    selector) composed with `assert_eq`; `hone` is the selector's one-hotness, which comes from
    `arithmetic::eqb` on the `nblocks` bit vector; `hreg` is the `mm_bits[(7 - j) * 32 + k]`
    layout, which `regOf_index` states. The conclusion is the hypothesis `meaning_of_blocks`
    takes. -/
theorem hsel_of_final_hash [Nontrivial F] (m n : Nat) (sel : Nat → F)
    (hbit : Nat → List Bool) (hOut : Nat → List Nat) (e : List Nat)
    (hn : 0 < n) (hnm : n ≤ m)
    (hone : ∀ b, b < m → sel b = if n = b + 1 then 1 else 0)
    (hreg : ∀ b, hbit b = regOf (hOut b))
    (hlen : (hOut (n - 1)).length = 8) (helen : e.length = 32)
    (hwb : ∀ u ∈ hOut (n - 1), u < 2 ^ 32) (heb : ∀ x ∈ e, x < 256)
    (hmux : ∀ k, k < 256 →
      oneHotSum m sel (fun b => emb ((hbit b).getD k false))
        = emb ((digestBits e).getD k false)) :
    bytesOfWords (hOut (n - 1)) = e := by
  have hbl : (hbit (n - 1)).length = 256 := by rw [hreg, regOf_length, hlen]
  have hdl : (digestBits e).length = 256 := by rw [digestBits, toBits_length, helen]
  refine bytesOfWords_of_regOf _ _ hlen helen hwb heb ?_
  rw [← hreg (n - 1)]
  refine List.ext_getElem (by rw [hbl, hdl]) fun k hk _ => ?_
  rw [hbl] at hk
  have hstep := (hmux k hk).symm.trans
    (oneHotSum_select m n sel (fun b => emb ((hbit b).getD k false)) hn hnm hone)
  have := emb_inj hstep
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
  exact this.symm

/-! ## Sanity

The conventions above are conventions; these pin them to concrete values. -/

/-- Least significant bit first: `0xA5 = 1010_0101` reads `1,0,1,0,0,1,0,1`. -/
theorem toBits_a5 : toBits 8 0xA5 = [true, false, true, false, false, true, false, true] := by decide

/-- Word 0 highest, and within a word big-endian bytes. -/
theorem beVal_two_words :
    beVal (bytesOfWords [0xdeadbeef, 0x01020304]) = 0xdeadbeef01020304 := by decide

/-- The register puts word 0 in the top 32 bits. -/
theorem bval_regOf_two : bval (regOf [1, 0]) = 2 ^ 32 := by decide

/-! ## Residual

One thing, and it is the artifact's.

* **Per-block compression.** `ChainOk`'s per-block `blockFrom` equation, for the mdoc circuit.
  `quadcert/Bridge/Sha256Gf2/` is being built to state exactly this over GF(2¹²⁸), but for the
  standalone one-block SHA-256 artifact; pointing it at mdoc needs the mdoc circuit ingested.

Two things this file does close, both listed as residual by `ShaChain`:

* **The one-hot selection.** `oneHotSum_select_vec` — the 8 × 32 muxes share one selector, so the
  register carries block `nblocks - 1` verbatim.

* **The byte order.** `regOf_index` states the Rust index map as a theorem, `bval_regOf` gives the
  register's value, and `bytesOfWords_of_regOf` turns the `assert_eq` into `ShaChain`'s `hsel`.
  `hsel_of_final_hash` is the two composed. `GoldenCheck.shaMso` and `GoldenChain.chain_digest`
  remain as independent checks of the same convention on real bytes.

Not an obligation but worth saying: `oneHotSum_select` takes the selector's one-hotness as `hsel`,
and that comes from `arithmetic::eqb` on the `nblocks` bit vector. `eqb` is `BitLt.base`'s *first*
component folded with `tree_andb`, so `Compare.lean`'s machinery already covers it — `bfold_spec`'s
first component is the equality, where the comparator used the second.
-/

end Mux
end MDoc
