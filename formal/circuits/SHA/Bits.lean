import SHA.Spec

/-!
# The per-bit algebra the wrapping-sum lemmas need

The 184 `assert_wrapping_sum_prime` assertions are the real content of the SHA-256 circuit. Each
reads five or six 32-bit words *as their bits* and asserts one wrapping sum. Measured on a
`schedule` assertion: 274 cone nodes over 161 inputs — `input_block{0,1,9,14}` and `outw0`, which
is exactly the specification's

    W[16] = σ₁(W[14]) + W[9] + σ₀(W[1]) + W[0]

The cone is **not** linear: a linearity probe at random points fails, because XOR on bits is
`a + b - 2ab` and `σ₀`/`σ₁` are built from it. So each meaning lemma carries the degree-2 bit
algebra of `σ`/`Σ`/`Ch`/`Maj`, and that algebra has to exist before the generator can emit
anything.

This module supplies it. The one fact everything rests on is that `bitAt` inverts `ofBits` on a
boolean list — which is what lets `zipBits f (ofBits xs) (ofBits ys)` become
`ofBits (zipWith f xs ys)`, turning a statement about 32-bit words into 32 independent statements
about bits. `Spec.lean` states the specification over bit lists precisely so this bridge is a
per-bit identity rather than a bitvector lemma.
-/

namespace SHA256

/-! ### `bitAt` inverts `ofBits` -/

theorem ofBits_cons (b : Nat) (bs : List Nat) : ofBits (b :: bs) = b + 2 * ofBits bs := rfl

theorem bitAt_zero (x : Nat) : bitAt x 0 = x % 2 := by
  simp [bitAt]

theorem bitAt_succ (x i : Nat) : bitAt x (i + 1) = bitAt (x / 2) i := by
  simp only [bitAt, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul]

/-- The heart of the bridge: reading bit `i` out of a packed boolean list gives entry `i` back. -/
theorem bitAt_ofBits : ∀ (bs : List Nat), (∀ b ∈ bs, IsBit b) → ∀ i,
    bitAt (ofBits bs) i = bs.getD i 0
  | [], _, i => by simp [ofBits, bitAt]
  | b :: bs, h, 0 => by
      have hb : IsBit b := h b (by simp)
      have : b < 2 := by rcases hb with rfl | rfl <;> omega
      simp only [ofBits_cons, bitAt_zero, List.getD_cons_zero]
      omega
  | b :: bs, h, i + 1 => by
      have hb : IsBit b := h b (by simp)
      have hlt : b < 2 := by rcases hb with rfl | rfl <;> omega
      have hdiv : (b + 2 * ofBits bs) / 2 = ofBits bs := by omega
      simp only [ofBits_cons, bitAt_succ, hdiv, List.getD_cons_succ]
      exact bitAt_ofBits bs (fun x hx => h x (by simp [hx])) i

/-! ### The bitwise operations, per bit

`zipBits` folds over `List.range 32`, so it is determined by the 32 values `bitAt x i`. Once
`bitAt_ofBits` replaces those by list entries, both sides are the same fold over the same data. -/

private theorem foldr_bit_congr (g h : Nat → Nat) :
    ∀ (l : List Nat), (∀ i ∈ l, g i = h i) →
      l.foldr (fun i acc => acc * 2 + g i) 0 = l.foldr (fun i acc => acc * 2 + h i) 0
  | [], _ => rfl
  | i :: rest, hgh => by
      simp only [List.foldr_cons, foldr_bit_congr g h rest (fun j hj => hgh j (by simp [hj])),
        hgh i (by simp)]

/-- `zipBits` depends on its arguments only through their first 32 bits. -/
theorem zipBits_congr (f : Nat → Nat → Nat) {x y x' y' : Nat}
    (hx : ∀ i, i < 32 → bitAt x i = bitAt x' i)
    (hy : ∀ i, i < 32 → bitAt y i = bitAt y' i) :
    zipBits f x y = zipBits f x' y' := by
  simp only [zipBits]
  exact foldr_bit_congr _ _ (List.range 32) fun i hi => by
    have h32 : i < 32 := List.mem_range.mp hi
    rw [hx i h32, hy i h32]

/-- Packing a boolean list and reading its bits back is the identity on the first `length` bits,
    which is the form `zipBits_congr` consumes. -/
theorem bitAt_ofBits_eq (bs : List Nat) (h : ∀ b ∈ bs, IsBit b) (i : Nat) :
    bitAt (ofBits bs) i = bs.getD i 0 :=
  bitAt_ofBits bs h i

/-! ### `zipBits` is a packed bit list

The payoff. `zipBits`'s fold over `range 32` builds `Σ_k f (bit x k) * 2 ^ k`, which is exactly
`ofBits` of the pointwise list — so a statement about a 32-bit word becomes 32 independent
statements about bits, and `bitAt_ofBits` reads them back. This is what makes the wrapping-sum
meaning lemmas degree-1 per bit instead of degree-2 in packed words. -/

private theorem foldr_eq_ofBits (g : Nat → Nat) :
    ∀ l : List Nat, l.foldr (fun i acc => acc * 2 + g i) 0 = ofBits (l.map g)
  | [] => rfl
  | i :: rest => by
      simp only [List.foldr_cons, List.map_cons, ofBits_cons, foldr_eq_ofBits g rest]
      omega

theorem zipBits_eq_ofBits (f : Nat → Nat → Nat) (x y : Nat) :
    zipBits f x y = ofBits ((List.range 32).map (fun i => f (bitAt x i) (bitAt y i))) :=
  foldr_eq_ofBits _ (List.range 32)

/-- Reading bit `i` of a `zipBits` result gives `f` applied to bit `i` of each argument —
    provided `f` returns bits, which every operation here does. -/
theorem bitAt_zipBits (f : Nat → Nat → Nat) (x y : Nat)
    (hf : ∀ a b, IsBit (f a b)) (i : Nat) (hi : i < 32) :
    bitAt (zipBits f x y) i = f (bitAt x i) (bitAt y i) := by
  rw [zipBits_eq_ofBits]
  rw [bitAt_ofBits _ (fun b hb => by
    simp only [List.mem_map] at hb
    obtain ⟨j, _, rfl⟩ := hb
    exact hf _ _)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]
  simp

/-! ### Shifts and rotations, as index arithmetic

`shr` and `rotr` move bit `i` to a different index. On the bit-list side that is `getD` at a
shifted index, so a generated lemma never has to reason about division by a power of two. -/

theorem bitAt_shr (n x i : Nat) : bitAt (shr n x) i = bitAt x (n + i) := by
  simp only [shr, bitAt, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- Bits below a power-of-two mask survive it. -/
theorem bitAt_mod (m x i : Nat) (hi : i < m) : bitAt (x % 2 ^ m) i = bitAt x i := by
  have hm : (2 : Nat) ^ m = 2 ^ i * 2 ^ (m - i) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdvd : (2 : Nat) ∣ 2 ^ (m - i) := by
    have he : m - i = (m - i - 1) + 1 := by omega
    rw [he, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
  simp only [bitAt, hm, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ hdvd

/-- Bits of a value below `2 ^ 32` are unaffected by `w32`. -/
theorem bitAt_w32 (x i : Nat) (hi : i < 32) : bitAt (w32 x) i = bitAt x i :=
  bitAt_mod 32 x i hi

/-! ### Rotation, as index arithmetic mod 32

`rotr` is the one operation whose bit index is not `i` or `i + n`, and it is the reason
`Sigma0`/`Sigma1`/`sigma0`/`sigma1` need anything beyond `bitAt_shr`. Once the wrap-around is
discharged here, every generated meaning lemma reads bit `(i + n) % 32` of a list and does no
arithmetic of its own. -/

/-- Adding a multiple of `2 ^ (i + 1)` leaves bit `i` alone. -/
private theorem bitAt_add_mul_two_pow (a c i : Nat) :
    bitAt (a + c * 2 ^ (i + 1)) i = bitAt a i := by
  simp only [bitAt, Nat.pow_succ', ← Nat.mul_assoc,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), Nat.add_mul_mod_self_right]

/-- The high `32 - n` bits and the low `n` bits of a 32-bit word, as the split both `rotr`
    lemmas divide along. -/
private theorem split_lt (n x : Nat) (hn : n ≤ 32) (hx : x < 2 ^ 32) :
    x / 2 ^ n < 2 ^ (32 - n) := by
  have hsplit : (2 : Nat) ^ n * 2 ^ (32 - n) = 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1; omega
  exact Nat.div_lt_of_lt_mul (by rw [hsplit]; exact hx)

/-- `rotr` in closed form on a 32-bit input: the low `n` bits move to the top, the rest down.
    Stated separately because the wrap-around case of `bitAt_rotr` reads it off directly. -/
theorem rotr_eq (n x : Nat) (hn : n ≤ 32) (hx : x < 2 ^ 32) :
    rotr n x = x / 2 ^ n + x % 2 ^ n * 2 ^ (32 - n) := by
  have hsplit : (2 : Nat) ^ n * 2 ^ (32 - n) = 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hq : x / 2 ^ n < 2 ^ (32 - n) := split_lt n x hn hx
  have hr : x % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  -- `x * 2 ^ (32 - n)` splits along the same division, and the high part is a multiple of `2 ^ 32`.
  have hmul : x * 2 ^ (32 - n) = x / 2 ^ n * 2 ^ 32 + x % 2 ^ n * 2 ^ (32 - n) := by
    calc x * 2 ^ (32 - n)
        = (2 ^ n * (x / 2 ^ n) + x % 2 ^ n) * 2 ^ (32 - n) := by
          rw [Nat.div_add_mod]
      _ = 2 ^ n * (x / 2 ^ n) * 2 ^ (32 - n) + x % 2 ^ n * 2 ^ (32 - n) := by
          rw [Nat.add_mul]
      _ = x / 2 ^ n * 2 ^ 32 + x % 2 ^ n * 2 ^ (32 - n) := by
          rw [Nat.mul_comm (2 ^ n) (x / 2 ^ n), Nat.mul_assoc, hsplit]
  -- The rotated value already fits in 32 bits, so the outer `w32` is the identity.
  have hlt : x / 2 ^ n + x % 2 ^ n * 2 ^ (32 - n) < 2 ^ 32 := by
    have h1 : (x % 2 ^ n + 1) * 2 ^ (32 - n) ≤ 2 ^ n * 2 ^ (32 - n) :=
      Nat.mul_le_mul_right _ hr
    rw [hsplit, Nat.add_mul, Nat.one_mul] at h1
    omega
  simp only [rotr, w32, hmul]
  omega

/-- The rotation lemma the `Sigma`/`sigma` meaning lemmas consume. -/
theorem bitAt_rotr (n x i : Nat) (hn : n ≤ 32) (hx : x < 2 ^ 32) (hi : i < 32) :
    bitAt (rotr n x) i = bitAt x ((i + n) % 32) := by
  have hq : x / 2 ^ n < 2 ^ (32 - n) := split_lt n x hn hx
  rw [rotr_eq n x hn hx]
  by_cases hc : i + n < 32
  · -- No wrap: bit `i` of the rotation sits in the shifted-down part, at index `i + n` of `x`.
    have hmod : (i + n) % 32 = i + n := Nat.mod_eq_of_lt hc
    have he : 32 - n - i - 1 + (i + 1) = 32 - n := by omega
    have hpow : x % 2 ^ n * 2 ^ (32 - n)
        = x % 2 ^ n * 2 ^ (32 - n - i - 1) * 2 ^ (i + 1) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, he]
    rw [hmod, hpow, bitAt_add_mul_two_pow, Nat.add_comm i n, ← bitAt_shr]
    rfl
  · -- Wrap: bit `i` lands in the part that came from the low `n` bits of `x`.
    have hmod : (i + n) % 32 = i + n - 32 := by omega
    have hpow : (2 : Nat) ^ i = 2 ^ (32 - n) * 2 ^ (i + n - 32) := by
      rw [← Nat.pow_add]; congr 1; omega
    simp only [bitAt, hmod, hpow, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos (32 - n)), Nat.div_eq_of_lt hq, Nat.zero_add]
    exact bitAt_mod n x (i + n - 32) (by omega)

/-- Sanity check on the index formula, independent of the proof: at every bit of one concrete
    rotation. `block_empty` already pins `rotr`'s *direction* through the whole compression
    function, but nothing there exercises `(i + n) % 32`, and an off-by-one in the wrap-around
    would still satisfy `rotr_eq`. -/
example : ∀ i ∈ List.range 32,
    bitAt (rotr 7 0x12345678) i = bitAt 0x12345678 ((i + 7) % 32) := by decide

end SHA256
