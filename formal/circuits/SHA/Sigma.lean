import Mathlib.Data.List.Basic
import SHA.Bits

/-!
# `σ₀`, `σ₁`, `Σ₀`, `Σ₁` as the circuit writes them

`SHA/Bits.lean` turns a 32-bit word into its bit list and moves indices around. This file spends
that toolkit on the four rotate-xor functions, which is the step the schedule and round bridges
need and the one the specification cannot take on its own.

## Why this is the hard direction

`xorW` is `zipBits` of `fun a b => a + b - 2 * a * b`. On bits that function *is* xor, and the
compiler emits it literally: a schedule assertion's `z` contains, for each output bit, an
intermediate node `a + b - 2ab` and then a second application against the third input. So the
circuit's polynomial and the specification's `σ₀` are the same object, but one is written as 51
degree-2 terms over 161 input bits and the other as three rotations of a packed word.

`sigma0_bits` is the bridge: it rewrites `σ₀ (ofBits bs)` into `ofBits` of the 32 pointwise
double-xors, at the exact indices `(j+7) % 32`, `(j+18) % 32` and `j+3` the circuit uses. After
it, a meaning lemma is `ring` over bits with no division, no modular arithmetic and no rotation.

`shr` is the reason the third index is `j + 3` rather than `(j + 3) % 32`: bits at or above 32
are shifted out, and `List.getD` past the end returns the same `0`.
-/

set_option maxRecDepth 20000

namespace SHA256

/-- The circuit's xor: `a + b - 2ab`, exactly the function `xorW` folds. Nat subtraction is safe
    because `2ab ≤ a + b` whenever `a` and `b` are bits. -/
def xb (a b : Nat) : Nat := a + b - 2 * a * b

theorem xb_isBit {a b : Nat} (ha : IsBit a) (hb : IsBit b) : IsBit (xb a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every `bitAt` is a bit. Needed because `bitAt_zipBits` asks for a totally bit-valued `f`,
    which `xb` is not — it is only bit-valued on bits. -/
theorem bitAt_isBit (x i : Nat) : IsBit (bitAt x i) := by
  have h : x / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by omega)
  show x / 2 ^ i % 2 = 0 ∨ x / 2 ^ i % 2 = 1
  omega

theorem bitAt_xorW (x y i : Nat) (hi : i < 32) :
    bitAt (xorW x y) i = xb (bitAt x i) (bitAt y i) := by
  rw [xorW, zipBits_eq_ofBits]
  rw [bitAt_ofBits _ (fun b hb => by
    simp only [List.mem_map] at hb
    obtain ⟨j, _, rfl⟩ := hb
    exact xb_isBit (bitAt_isBit _ _) (bitAt_isBit _ _))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]
  rfl

/-- A word built from 32 bits is in range, which every rotation lemma needs. -/
theorem ofBits_lt32 {bs : List Nat} (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b) :
    ofBits bs < 2 ^ 32 := by
  have := ofBits_lt bs hb; rwa [hlen] at this

/-- **The three-way rotate-xor, on bits.** `r₁`, `r₂` are rotations and `sh` is either a third
    rotation (for `Σ₀`/`Σ₁`) or a shift (for `σ₀`/`σ₁`); the two cases differ only in the third
    index, so both specialise this. -/
private theorem xor3_bits (bs : List Nat) (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b)
    (r₁ r₂ : Nat) (h₁ : r₁ ≤ 32) (h₂ : r₂ ≤ 32) (third : Nat → Nat)
    (hthird : ∀ i, i < 32 → bitAt (ofBits bs) (third i) = bs.getD (third i) 0)
    (t : Nat) (ht : ∀ i, i < 32 → bitAt t i = bitAt (ofBits bs) (third i)) :
    xorW (xorW (rotr r₁ (ofBits bs)) (rotr r₂ (ofBits bs))) t
      = ofBits ((List.range 32).map (fun j =>
          xb (xb (bs.getD ((j + r₁) % 32) 0) (bs.getD ((j + r₂) % 32) 0)) (bs.getD (third j) 0))) := by
  have hx : ofBits bs < 2 ^ 32 := ofBits_lt32 hlen hb
  rw [xorW, zipBits_eq_ofBits]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  show xb _ _ = _
  rw [bitAt_xorW _ _ i hi32, bitAt_rotr r₁ _ i h₁ hx hi32, bitAt_rotr r₂ _ i h₂ hx hi32,
    ht i hi32, hthird i hi32, bitAt_ofBits_eq bs hb, bitAt_ofBits_eq bs hb]

/-- `σ₀ x = (x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x >> 3)`, per output bit. -/
theorem sigma0_bits (bs : List Nat) (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b) :
    sigma0 (ofBits bs)
      = ofBits ((List.range 32).map (fun j =>
          xb (xb (bs.getD ((j + 7) % 32) 0) (bs.getD ((j + 18) % 32) 0)) (bs.getD (j + 3) 0))) := by
  refine xor3_bits bs hlen hb 7 18 (by omega) (by omega) (fun j => j + 3)
    (fun i _ => bitAt_ofBits_eq bs hb _) _ (fun i _ => ?_)
  rw [bitAt_shr, Nat.add_comm 3 i]

/-- `σ₁ x = (x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x >> 10)`, per output bit. -/
theorem sigma1_bits (bs : List Nat) (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b) :
    sigma1 (ofBits bs)
      = ofBits ((List.range 32).map (fun j =>
          xb (xb (bs.getD ((j + 17) % 32) 0) (bs.getD ((j + 19) % 32) 0)) (bs.getD (j + 10) 0))) := by
  refine xor3_bits bs hlen hb 17 19 (by omega) (by omega) (fun j => j + 10)
    (fun i _ => bitAt_ofBits_eq bs hb _) _ (fun i _ => ?_)
  rw [bitAt_shr, Nat.add_comm 10 i]

/-- `Σ₀ x = (x ⋙ 2) ⊕ (x ⋙ 13) ⊕ (x ⋙ 22)`, per output bit. -/
theorem Sigma0_bits (bs : List Nat) (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b) :
    Sigma0 (ofBits bs)
      = ofBits ((List.range 32).map (fun j =>
          xb (xb (bs.getD ((j + 2) % 32) 0) (bs.getD ((j + 13) % 32) 0))
             (bs.getD ((j + 22) % 32) 0))) := by
  refine xor3_bits bs hlen hb 2 13 (by omega) (by omega) (fun j => (j + 22) % 32)
    (fun i _ => bitAt_ofBits_eq bs hb _) _ (fun i hi => ?_)
  exact bitAt_rotr 22 _ i (by omega) (ofBits_lt32 hlen hb) hi

/-- `Σ₁ x = (x ⋙ 6) ⊕ (x ⋙ 11) ⊕ (x ⋙ 25)`, per output bit. -/
theorem Sigma1_bits (bs : List Nat) (hlen : bs.length = 32) (hb : ∀ b ∈ bs, IsBit b) :
    Sigma1 (ofBits bs)
      = ofBits ((List.range 32).map (fun j =>
          xb (xb (bs.getD ((j + 6) % 32) 0) (bs.getD ((j + 11) % 32) 0))
             (bs.getD ((j + 25) % 32) 0))) := by
  refine xor3_bits bs hlen hb 6 11 (by omega) (by omega) (fun j => (j + 25) % 32)
    (fun i _ => bitAt_ofBits_eq bs hb _) _ (fun i hi => ?_)
  exact bitAt_rotr 25 _ i (by omega) (ofBits_lt32 hlen hb) hi

/-! ### `Ch` and `Maj`, on bits

The round assertions need what `σ` needed, for the other two round functions. Measured on the
artifact, the compiler emits `Ch` as 64 degree-2 terms over the `e`,`f` and `e`,`g` bit pairs
(plus the linear `g`), and `Maj` via `a∧b` together with `c ∧ (a⊕b)` — so both are degree 2 in
the witnessed bits, never degree 3, and both are bit-valued.

`chb`/`majb` are written the way `SHA/Spec.lean` writes them, out of `andW`, `notW` and `xorW`;
`chb_eq`/`majb_eq` then give the circuit's spelling. Keeping the two apart is the point: one side
has to match the standard, the other has to match the compiler. -/

/-- `Ch`'s output bit, as the specification composes it. -/
def chb (a b c : Nat) : Nat := xb (a * b) ((1 - a) * c)

/-- `Maj`'s output bit, as the specification composes it. -/
def majb (a b c : Nat) : Nat := xb (xb (a * b) (a * c)) (b * c)

theorem chb_isBit {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) : IsBit (chb a b c) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    (unfold IsBit; decide)

theorem majb_isBit {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    IsBit (majb a b c) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    (unfold IsBit; decide)

/-- The circuit's spelling of `Ch`: `g + e·f - e·g`, one linear and two quadratic terms. -/
theorem chb_eq {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    chb a b c = c + a * b - a * c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-- The circuit's spelling of `Maj`: `a·b + c·(a ⊕ b)`. The two summands are never both `1`, so
    no xor is needed at the top. -/
theorem majb_eq {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    majb a b c = a * b + c * xb a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-- `Maj` is symmetric in its first two arguments. Needed because the compiler picks the order of
    the `a ⊕ b` mid's legs per bit — measured on the artifact, 1,100 of the 2,048 Maj mids take
    `a` first and the other 948 take `b`. -/
theorem majb_comm {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    majb a b c = majb b a c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

theorem bitAt_andW (x y i : Nat) (hi : i < 32) :
    bitAt (andW x y) i = bitAt x i * bitAt y i := by
  rw [andW, zipBits_eq_ofBits]
  rw [bitAt_ofBits _ (fun b hb => by
    simp only [List.mem_map] at hb
    obtain ⟨j, _, rfl⟩ := hb
    rcases bitAt_isBit x j with h | h <;> rcases bitAt_isBit y j with h' | h' <;>
      simp [h, h', IsBit])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]
  rfl

/-- Complementing within `m` bits complements every bit below `m`. Stated for a general width
    because the induction has to shrink it; `notW` is the case `m = 32`. -/
theorem bitAt_compl : ∀ (m x : Nat), x < 2 ^ m → ∀ i, i < m →
    bitAt (2 ^ m - 1 - x) i = 1 - bitAt x i
  | 0, _, _, _, hi => absurd hi (by omega)
  | m + 1, x, hx, 0, _ => by
      have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      have hm : (1 : Nat) ≤ 2 ^ m := Nat.one_le_two_pow
      simp only [bitAt_zero]
      omega
  | m + 1, x, hx, i + 1, hi => by
      have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      have hm : (1 : Nat) ≤ 2 ^ m := Nat.one_le_two_pow
      have hdiv : (2 ^ (m + 1) - 1 - x) / 2 = 2 ^ m - 1 - x / 2 := by omega
      have hxlt : x / 2 < 2 ^ m := by omega
      rw [bitAt_succ, hdiv, bitAt_succ, bitAt_compl m (x / 2) hxlt i (by omega)]

theorem bitAt_notW (x i : Nat) (hx : x < 2 ^ 32) (hi : i < 32) :
    bitAt (notW x) i = 1 - bitAt x i := by
  have h1 : (2 : Nat) ^ 32 - 1 - w32 x = 2 ^ 32 - 1 - x := by
    rw [w32, Nat.mod_eq_of_lt hx]
  rw [notW, h1, bitAt_compl 32 x hx i hi]

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)`, per output bit. -/
theorem Ch_bits (xs ys zs : List Nat) (hxl : xs.length = 32)
    (hxb : ∀ b ∈ xs, IsBit b) (hyb : ∀ b ∈ ys, IsBit b) (hzb : ∀ b ∈ zs, IsBit b) :
    Ch (ofBits xs) (ofBits ys) (ofBits zs)
      = ofBits ((List.range 32).map (fun j =>
          chb (xs.getD j 0) (ys.getD j 0) (zs.getD j 0))) := by
  have hx : ofBits xs < 2 ^ 32 := ofBits_lt32 hxl hxb
  rw [Ch, xorW, zipBits_eq_ofBits]
  refine congrArg ofBits (List.map_congr_left ?_)
  intro i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  show xb _ _ = _
  rw [bitAt_andW _ _ i hi32, bitAt_andW _ _ i hi32, bitAt_notW _ i hx hi32,
    bitAt_ofBits_eq xs hxb, bitAt_ofBits_eq ys hyb, bitAt_ofBits_eq zs hzb]
  rfl

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`, per output bit. -/
theorem Maj_bits (xs ys zs : List Nat)
    (hxb : ∀ b ∈ xs, IsBit b) (hyb : ∀ b ∈ ys, IsBit b) (hzb : ∀ b ∈ zs, IsBit b) :
    Maj (ofBits xs) (ofBits ys) (ofBits zs)
      = ofBits ((List.range 32).map (fun j =>
          majb (xs.getD j 0) (ys.getD j 0) (zs.getD j 0))) := by
  rw [Maj, xorW, zipBits_eq_ofBits]
  refine congrArg ofBits (List.map_congr_left ?_)
  intro i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  show xb _ _ = _
  rw [bitAt_xorW _ _ i hi32, bitAt_andW _ _ i hi32, bitAt_andW _ _ i hi32,
    bitAt_andW _ _ i hi32, bitAt_ofBits_eq xs hxb, bitAt_ofBits_eq ys hyb,
    bitAt_ofBits_eq zs hzb]
  rfl

/-! ### `xb` is addition mod 2

The circuit is free to xor the three legs of a `σ` in any order and any grouping — measured on
the artifact it varies by instance. Rather than carry six permutation lemmas, note that on bits
`xb` *is* `+ % 2`, which is commutative and associative for free. -/

theorem xb_eq_mod {a b : Nat} (ha : IsBit a) (hb : IsBit b) : xb a b = (a + b) % 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

theorem xb3_eq_mod {a b c : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c) :
    xb (xb a b) c = (a + b + c) % 2 := by
  rw [xb_eq_mod (xb_isBit ha hb) hc, xb_eq_mod ha hb]
  omega

/-- Any grouping and order of the three legs gives the same bit. -/
theorem xb3_perm {a b c a' b' c' : Nat} (ha : IsBit a) (hb : IsBit b) (hc : IsBit c)
    (ha' : IsBit a') (hb' : IsBit b') (hc' : IsBit c')
    (h : a + b + c = a' + b' + c') :
    xb (xb a b) c = xb (xb a' b') c' := by
  rw [xb3_eq_mod ha hb hc, xb3_eq_mod ha' hb' hc', h]

/-! ### Sanity checks

The index formulas are the part a reader cannot verify by inspection, and `block_empty` in
`SHA/Spec.lean` does not exercise them independently — it would still pass if two rotations were
swapped. These check all four against a concrete word, by the kernel. -/

private def w0 : List Nat :=
  [0,1,1,0, 1,0,1,0, 0,0,1,1, 1,1,0,1, 0,1,0,1, 1,0,0,1, 1,1,0,0, 0,1,1,0]

example : sigma0 (ofBits w0)
    = ofBits ((List.range 32).map (fun j =>
        xb (xb (w0.getD ((j + 7) % 32) 0) (w0.getD ((j + 18) % 32) 0)) (w0.getD (j + 3) 0))) := by
  decide

example : sigma1 (ofBits w0)
    = ofBits ((List.range 32).map (fun j =>
        xb (xb (w0.getD ((j + 17) % 32) 0) (w0.getD ((j + 19) % 32) 0)) (w0.getD (j + 10) 0))) := by
  decide

example : Sigma0 (ofBits w0)
    = ofBits ((List.range 32).map (fun j =>
        xb (xb (w0.getD ((j + 2) % 32) 0) (w0.getD ((j + 13) % 32) 0)) (w0.getD ((j + 22) % 32) 0))) := by
  decide

private def w1 : List Nat :=
  [1,1,0,0, 1,0,0,1, 0,1,1,0, 1,0,1,0, 1,1,1,0, 0,0,1,1, 0,1,0,1, 1,0,0,1]
private def w2 : List Nat :=
  [0,1,0,1, 1,1,0,0, 1,0,0,1, 0,1,1,1, 0,0,1,0, 1,1,0,1, 0,0,1,1, 1,0,1,0]

example : Ch (ofBits w0) (ofBits w1) (ofBits w2)
    = ofBits ((List.range 32).map (fun j => chb (w0.getD j 0) (w1.getD j 0) (w2.getD j 0))) := by
  decide

example : Maj (ofBits w0) (ofBits w1) (ofBits w2)
    = ofBits ((List.range 32).map (fun j => majb (w0.getD j 0) (w1.getD j 0) (w2.getD j 0))) := by
  decide

example : Sigma1 (ofBits w0)
    = ofBits ((List.range 32).map (fun j =>
        xb (xb (w0.getD ((j + 6) % 32) 0) (w0.getD ((j + 11) % 32) 0)) (w0.getD ((j + 25) % 32) 0))) := by
  decide

end SHA256
