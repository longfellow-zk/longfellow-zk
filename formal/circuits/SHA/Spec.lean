set_option maxRecDepth 100000

/-!
# SHA-256, as a specification

The analogue of `ECDSA/EcdsaSpec.lean` for the one-block SHA-256 circuit: what the circuit is
supposed to compute, written without reference to any circuit. Nothing here mentions wires,
assertions, or the compiler; it is FIPS 180-4 section 6.2.2 transcribed.

Everything is on `Nat` with an explicit `% 2 ^ 32` rather than on `UInt32`, because the circuit
proves its statements about field elements carrying 32-bit values and the bridge will be
`Nat`-shaped. `w32` is applied at every point the standard says "addition is modulo 2^32", and
nowhere else, so a reader can check the correspondence line by line.

## What the circuit's assertions look like

Measured on the current artifact (6,840 assertions, four path families):

| family | count | cone |
|---|---:|---:|
| `is_boolean` | 6,656 | 3 nodes |
| `sha256/rounds/N/round_step/assert_wrapping_sum_prime` | 128 | 307 nodes, 225 inputs |
| `sha256/schedule/N/assert_wrapping_sum_prime` | 48 | 274 nodes, 161 inputs |
| `sha256/final/N/assert_wrapping_sum_prime` | 8 | ~274 nodes |

So the circuit witnesses every 32-bit word **as its 32 bits**, asserts each is boolean, and
asserts one wrapping sum per word it computes. `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁` never appear as
their own assertions -- they are linear combinations of bits inside a wrapping sum. That is why
the witness predicate below is stated over *bit lists*: it is the shape the circuit actually
constrains, and it keeps the eventual meaning lemmas degree-1 in the witness.
-/

namespace SHA256

/-- Reduce to 32 bits. -/
def w32 (x : Nat) : Nat := x % 2 ^ 32

/-- Bit `i` of a 32-bit word, least significant first. -/
def bitAt (x i : Nat) : Nat := x / 2 ^ i % 2

/-- Rotate right within 32 bits. -/
def rotr (n x : Nat) : Nat := w32 (x / 2 ^ n + x * 2 ^ (32 - n))

/-- Shift right. -/
def shr (n x : Nat) : Nat := x / 2 ^ n

/-! ### Bitwise operations, defined on bits

`Nat.land`/`lxor` exist, but the circuit constrains bits individually, so stating the spec over
bits is what makes the bridge a per-bit identity rather than a bitvector lemma. -/

/-- Bitwise combine two 32-bit words with a two-bit function.

    `foldr` over `range 32` visits `i = 31` first with `acc = 0`, so writing `acc * 2 + f (bit i)`
    accumulates `Σ f (bit k) * 2 ^ k` — little-endian, matching `ofBits` and the circuit. Using
    `bit (31 - i)` here instead reverses every word, which is exactly the bug the empty-string
    test vector catches. -/
def zipBits (f : Nat → Nat → Nat) (x y : Nat) : Nat :=
  (List.range 32).foldr (fun i acc => acc * 2 + f (bitAt x i) (bitAt y i)) 0

def andW (x y : Nat) : Nat := zipBits (fun a b => a * b) x y
def xorW (x y : Nat) : Nat := zipBits (fun a b => a + b - 2 * a * b) x y
def notW (x : Nat) : Nat := 2 ^ 32 - 1 - w32 x

/-! ### The round functions, FIPS 180-4 §4.1.2 -/

def Ch (x y z : Nat) : Nat := xorW (andW x y) (andW (notW x) z)
def Maj (x y z : Nat) : Nat := xorW (xorW (andW x y) (andW x z)) (andW y z)
def Sigma0 (x : Nat) : Nat := xorW (xorW (rotr 2 x) (rotr 13 x)) (rotr 22 x)
def Sigma1 (x : Nat) : Nat := xorW (xorW (rotr 6 x) (rotr 11 x)) (rotr 25 x)
def sigma0 (x : Nat) : Nat := xorW (xorW (rotr 7 x) (rotr 18 x)) (shr 3 x)
def sigma1 (x : Nat) : Nat := xorW (xorW (rotr 17 x) (rotr 19 x)) (shr 10 x)

/-- The 64 round constants, FIPS 180-4 §4.2.2. -/
def K : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value, FIPS 180-4 §5.3.3. -/
def H0 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ### The message schedule

`W t = M t` for `t < 16`, and `W t = σ₁ (W (t-2)) + W (t-7) + σ₀ (W (t-15)) + W (t-16)` after,
all modulo `2 ^ 32`. Written as a fold producing the list in order, so that the 48 `schedule`
assertions line up one-to-one with the steps. -/

def scheduleStep (w : List Nat) : List Nat :=
  let n := w.length
  -- `at` is a keyword; `back k` is `W (n - k)`, the standard's backward reference.
  let back (k : Nat) : Nat := w.getD (n - k) 0
  w ++ [w32 (sigma1 (back 2) + back 7 + sigma0 (back 15) + back 16)]

def schedule : Nat → List Nat → List Nat
  | 0, w => w
  | n + 1, w => schedule n (scheduleStep w)

/-- The 64-word message schedule of a 16-word block. -/
def W (m : List Nat) : List Nat := schedule 48 m

/-! ### The compression function -/

/-- One round, on the eight working variables. -/
def round (t : Nat) (wt : Nat) (s : List Nat) : List Nat :=
  let a := s.getD 0 0; let b := s.getD 1 0; let c := s.getD 2 0; let d := s.getD 3 0
  let e := s.getD 4 0; let f := s.getD 5 0; let g := s.getD 6 0; let h := s.getD 7 0
  let t1 := w32 (h + Sigma1 e + Ch e f g + K.getD t 0 + wt)
  let t2 := w32 (Sigma0 a + Maj a b c)
  [w32 (t1 + t2), a, b, c, w32 (d + t1), e, f, g]

def rounds : Nat → List Nat → List Nat → List Nat
  | 0, _, s => s
  | n + 1, w, s => rounds n w (round (64 - (n + 1)) (w.getD (64 - (n + 1)) 0) s)

/-- **The one-block transform.** `m` is the 16-word message block; the result is the eight-word
    digest, which for a single block is `H0 + compress(H0, m)` componentwise modulo `2 ^ 32`. -/
def blockFrom (h : List Nat) (m : List Nat) : List Nat :=
  let s := rounds 64 (W m) h
  (List.range 8).map (fun i => w32 (h.getD i 0 + s.getD i 0))

def block (m : List Nat) : List Nat := blockFrom H0 m

/-! ### The witness predicate

The shape the circuit constrains: every 32-bit quantity appears as its 32 bits, each asserted
boolean, and each computed word is asserted equal to a wrapping sum of the things feeding it.
`ofBits` is how a bit list becomes the word the spec talks about, and it is the only place the
two vocabularies meet. -/

/-- Least-significant-first bit list to a natural. Matches the circuit's `as_eltw_unsafe`
    weighting, and `ECDSA2.bitsLE`'s on the field side. -/
def ofBits : List Nat → Nat
  | [] => 0
  | b :: bs => b + 2 * ofBits bs

def IsBit (b : Nat) : Prop := b = 0 ∨ b = 1

/-- A witnessed 32-bit word: 32 boolean bits. -/
structure Word32 where
  bits : List Nat
  len : bits.length = 32
  bool : ∀ b ∈ bits, IsBit b

def Word32.val (w : Word32) : Nat := ofBits w.bits

theorem ofBits_lt : ∀ (bs : List Nat), (∀ b ∈ bs, IsBit b) → ofBits bs < 2 ^ bs.length
  | [], _ => by simp [ofBits]
  | b :: bs, h => by
      have hb : IsBit b := h b (by simp)
      have hrest : ofBits bs < 2 ^ bs.length :=
        ofBits_lt bs (fun x hx => h x (by simp [hx]))
      have : b ≤ 1 := by rcases hb with rfl | rfl <;> omega
      simp only [ofBits, List.length_cons, Nat.pow_succ]
      omega

/-- A witnessed word is in range, which is what makes `w32` a no-op on it. -/
theorem Word32.val_lt (w : Word32) : w.val < 2 ^ 32 := by
  have := ofBits_lt w.bits w.bool
  rwa [w.len] at this

theorem Word32.w32_val (w : Word32) : w32 w.val = w.val :=
  Nat.mod_eq_of_lt w.val_lt

/-! ### Test vector

A transcription of a standard is worth exactly what its test vectors say it is. This one is
checked by the kernel, not by `#eval` or `native_decide`, so it is a permanent regression guard:
the padded empty message must hash to
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

It has already earned its keep — the first draft of `zipBits` indexed bits as `31 - i` and
produced `61d7f4ca…`, which nothing else in the file would have caught. -/

/-- SHA-256 padding of the empty message: one `1` bit, then zeros, then a 64-bit length of 0. -/
def emptyBlock : List Nat := [0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem block_empty :
    block emptyBlock = [0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
                        0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855] := by
  rfl

end SHA256
