/-
# Chunked equality

The last of `Assertions.lean`'s three arithmetic gadget obligations. Fourteen of the hash
circuit's 73 assertion families are `chunk_eq` — `bytes_at`, `key_eq`, `hash_eq`, `len_eq`,
`first_segment_start`, `cbor_len_eq` — and two more on the signature side. Every one of them is
written in `Asserted` as an equality of *bytes* or *bit vectors*, and what the circuit asserts is
an equality of **field elements**.

## What the circuit does

`arithmetic::assert_eq` does not compare bit vectors bit by bit. It packs them:

```rust
let k = n.div_ceil(dim);                        // dim = field.pseudo_dimension()
…
let chunk_size = remaining_n / remaining_k;     // as equal as they divide
let elt_a = self.as_eltw_field(chunk_a);        // Σ pseudo_basis(i) · bitᵢ
let elt_b = self.as_eltw_field(chunk_b);
self.logic.assert_eq("chunk_eq", &elt_a, &elt_b)
```

One field equation per chunk of at most `dim` bits. So the obligation is that
`Σ pseudo_basis(i) · bitᵢ` is **injective** on `{0,1}`-vectors of length at most `dim` — call it
`Separates` — and that the chunking really does keep every chunk within `dim`.

Injectivity is the whole content, and it is a different theorem in each field:

* **GF(2¹²⁸)**, which the hash circuit compiles to. `pseudo_basis(i) = 1 <<< i` is the bit
  pattern of `xⁱ`, so the sum is `eval α` of the bits read as a polynomial, and injectivity is
  `GF128.eval_injOn` — ultimately the irreducibility of `x¹²⁸ + x⁷ + x² + x + 1`.
* **𝔽ₚ₂₅₆**, which the signature circuit compiles to. `pseudo_basis(i) = 2ⁱ mod p` and
  `dim = bits(p) − 1`, so every chunk's value is below `2^(bits(p) − 1) ≤ p` and injectivity is
  just that `Nat.cast` does not wrap.

The second is why `dim` is `bits(p) − 1` and not `bits(p)`: one more bit and two different chunks
could differ by exactly `p`.

## Booleanity is load-bearing here

`Separates` quantifies over `List Bool`. Over arbitrary field elements the packing is nowhere
near injective — `2·1 = 1·2` — so it is `is_boolean` on every input wire that makes `chunk_eq`
mean bitwise equality at all. This is the clause where the 284,703 booleanity assertions do their
work, and it is why they are a hypothesis of the whole layer rather than a clause of it.
-/

import Mathlib
import mdoc.Spec
import ECDSA.BitLt
import GF128.Indep

namespace MDoc
namespace ChunkEq

open ECDSA2.BitLt

/-! ## The packing -/

variable {F : Type*}

/-- A bit as a field element. `BitLt.enc` is the same map, but over `Field`; `GF128` works over
    `CommRing`, so it is restated here rather than coupling the two class hierarchies. -/
def bit [CommRing F] (b : Bool) : F := if b then 1 else 0

/-- `as_eltw_field`: `Σᵢ pseudo_basis(i) · bitᵢ`, with the index threaded so the recursion matches
    the `Vec` the circuit builds. -/
def eltSum [CommRing F] (c : Nat → F) : Nat → List Bool → F
  | _, [] => 0
  | i, x :: xs => c i * bit x + eltSum c (i + 1) xs

@[simp] theorem bval_false (xs : List Bool) : bval (false :: xs) = 2 * bval xs := by simp [bval]

@[simp] theorem bval_true (xs : List Bool) : bval (true :: xs) = 1 + 2 * bval xs := by simp [bval]

/-- A bit list's value is below `2 ^ length`. -/
theorem bval_lt : ∀ l : List Bool, bval l < 2 ^ l.length
  | [] => by simp [bval]
  | x :: xs => by
      have ih := bval_lt xs
      simp only [bval, List.length_cons, pow_succ]
      cases x <;> simp <;> omega

/-- **The property `assert_eq` needs.** The basis separates `{0,1}`-vectors up to `dim` bits. -/
def Separates [CommRing F] (c : Nat → F) (dim : Nat) : Prop :=
  ∀ a b : List Bool, a.length = b.length → a.length ≤ dim →
    eltSum c 0 a = eltSum c 0 b → a = b

/-! ## The prime-field instance

`pseudo_basis(i) = 2ⁱ mod p`, and `dim = bits(p) − 1` keeps every chunk's value below `p`. -/

section Prime

variable [CommRing F]

/-- The packing is the bit list's value, cast. -/
theorem eltSum_two_pow (i : Nat) : ∀ l : List Bool,
    eltSum (fun j => (2 : F) ^ j) i l = (2 : F) ^ i * ((bval l : Nat) : F)
  | [] => by simp [eltSum, bval]
  | x :: xs => by
      have ih := eltSum_two_pow (i + 1) xs
      show (2 : F) ^ i * bit x + eltSum (fun j => (2 : F) ^ j) (i + 1) xs = _
      rw [ih]
      cases x <;> simp [bit, bval, pow_succ] <;> ring

/-- **𝔽ₚ separates.** With `dim` bits the value is below `2 ^ dim`, and if that is below the
    characteristic the cast cannot wrap. -/
theorem separates_prime (p dim : Nat) [CharP F p]
    (hdim : 2 ^ dim ≤ p) : Separates (fun j => (2 : F) ^ j) dim := by
  have key : ∀ u v : Nat, u < p → v < p → v ≤ u → ((u : F) = (v : F)) → u = v := by
    intro u v hu hv hvu he
    have hsub : ((u - v : Nat) : F) = 0 := by
      rw [Nat.cast_sub hvu, he, sub_self]
    have hdvd : p ∣ (u - v) := (CharP.cast_eq_zero_iff F p _).mp hsub
    rcases Nat.eq_zero_or_pos (u - v) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
  intro a b hlen hle heq
  rw [eltSum_two_pow 0 a, eltSum_two_pow 0 b] at heq
  simp only [pow_zero, one_mul] at heq
  have hba : bval a < p := lt_of_lt_of_le
    (lt_of_lt_of_le (bval_lt a) (Nat.pow_le_pow_right (by omega) hle)) hdim
  have hbb : bval b < p := lt_of_lt_of_le
    (lt_of_lt_of_le (bval_lt b) (Nat.pow_le_pow_right (by omega) (hlen ▸ hle))) hdim
  have hv : bval a = bval b := by
    rcases Nat.le_total (bval b) (bval a) with h | h
    · exact key _ _ hba hbb h heq
    · exact (key _ _ hbb hba h heq.symm).symm
  exact bval_inj a b hlen hv

end Prime

/-! ## The GF(2¹²⁸) instance

`pseudo_basis(i) = 1 <<< i` is the bit pattern of `xⁱ`, so the packing is `GF128.eval` of the
chunk read as a polynomial, and `GF128.eval_injOn` is exactly `Separates`. -/

section Gf2

variable [CommRing F] [CharP F 2]

/-- The packing is `eval` of the bits. Both sides are Horner from the low bit; this is the
    identification that makes `GF128`'s theory apply to `as_eltw_field`. -/
theorem eltSum_eval (α : F) (i : Nat) : ∀ l : List Bool,
    eltSum (fun j => α ^ j) i l = α ^ i * GF128.eval α (bval l)
  | [] => by simp [eltSum, bval]
  | x :: xs => by
      have ih := eltSum_eval α (i + 1) xs
      have hstep : GF128.eval α (bval (x :: xs))
          = bit x + α * GF128.eval α (bval xs) := by
        by_cases hz : bval (x :: xs) = 0
        · have hx : x = false := by cases x with
            | false => rfl
            | true => simp at hz
          subst hx
          have hxs : bval xs = 0 := by simp at hz; omega
          simp [hz, hxs, bit]
        · rw [GF128.eval_step α hz]
          have hbit : (bval (x :: xs)).testBit 0 = x := by
            cases x <;> simp [Nat.testBit_zero] <;> omega
          have hdiv : bval (x :: xs) / 2 = bval xs := by cases x <;> simp <;> omega
          rw [hbit, hdiv]
          cases x <;> simp [bit]
      show α ^ i * bit x + eltSum (fun j => α ^ j) (i + 1) xs = _
      rw [ih, hstep, pow_succ]
      ring

/-- **GF(2¹²⁸) separates**, up to its full 128 bits. -/
theorem separates_gf128 (α : F) (h : GF128.IsGen α) :
    Separates (fun j => α ^ j) 128 := by
  intro a b hlen hle heq
  rw [eltSum_eval α 0 a, eltSum_eval α 0 b] at heq
  simp only [pow_zero, one_mul] at heq
  have hba : bval a < 2 ^ 128 := lt_of_lt_of_le (bval_lt a) (Nat.pow_le_pow_right (by omega) hle)
  have hbb : bval b < 2 ^ 128 :=
    lt_of_lt_of_le (bval_lt b) (Nat.pow_le_pow_right (by omega) (hlen ▸ hle))
  have _hkeep := hlen
  exact bval_inj a b hlen (GF128.eval_injOn α h hba hbb heq)

end Gf2

/-! ## From chunks to the whole

`assert_eq` emits one equation per chunk; the clause wants the bit lists. -/

section Chunks

variable [CommRing F]

/-- **Chunkwise equality is equality.** Given a common splitting whose pieces are within `dim`,
    the per-chunk assertions determine the concatenation. -/
theorem eq_of_chunks (c : Nat → F) (dim : Nat) (hsep : Separates c dim) :
    ∀ (as bs : List (List Bool)), as.length = bs.length →
      (∀ i, i < as.length →
        (as.getD i []).length = (bs.getD i []).length ∧ (as.getD i []).length ≤ dim) →
      (∀ i, i < as.length → eltSum c 0 (as.getD i []) = eltSum c 0 (bs.getD i [])) →
      as.flatten = bs.flatten
  | [], [], _, _, _ => rfl
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | a :: as, b :: bs, hlen, hsize, heq => by
      have hl : as.length = bs.length := by simpa using hlen
      have h0 := hsize 0 (by simp)
      have hab : a = b := hsep a b h0.1 h0.2 (heq 0 (by simp))
      have hrest : as.flatten = bs.flatten :=
        eq_of_chunks c dim hsep as bs hl
          (fun i hi => hsize (i + 1) (by simpa using hi))
          (fun i hi => heq (i + 1) (by simpa using hi))
      simp only [List.flatten_cons, hab, hrest]

end Chunks

/-! ## The chunking, pinned

```rust
let k = n.div_ceil(dim);
let chunk_size = remaining_n / remaining_k;
```

Every chunk must come out at most `dim` wide, or `Separates` does not apply to it. That is not
obvious from the code — the sizes are `remaining_n / remaining_k`, a floor, recomputed each
round — so it is proved rather than assumed. -/

/-- The Rust loop's chunk sizes, in order. `k` is `remaining_k`. -/
def chunkSizes : Nat → Nat → List Nat
  | _, 0 => []
  | n, k + 1 => n / (k + 1) :: chunkSizes (n - n / (k + 1)) k

/-- The sizes tile the bit list: nothing is dropped and nothing is counted twice. -/
theorem chunkSizes_sum : ∀ (k n : Nat), (k = 0 → n = 0) → (chunkSizes n k).sum = n
  | 0, n, h => by simpa [chunkSizes] using (h rfl).symm
  | k + 1, n, _ => by
      have hle : n / (k + 1) ≤ n := Nat.div_le_self _ _
      have hrec := chunkSizes_sum k (n - n / (k + 1)) (by
        intro hk; subst hk; simp only [Nat.zero_add, Nat.div_one]; omega)
      simp only [chunkSizes, List.sum_cons, hrec]
      omega

/-- **No chunk exceeds `dim`.** With `k = ⌈n / dim⌉` rounds, the floor sizes stay within `dim`,
    which is what lets `Separates` apply to each `chunk_eq`. -/
theorem chunkSizes_le : ∀ (k n dim : Nat), n ≤ k * dim → ∀ s ∈ chunkSizes n k, s ≤ dim
  | 0, n, dim, _, s, hs => by simp [chunkSizes] at hs
  | k + 1, n, dim, hn, s, hs => by
      have hdm := Nat.div_add_mod n (k + 1)
      have hmod : n % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
      have hexp1 : (k + 1) * (n / (k + 1)) = k * (n / (k + 1)) + n / (k + 1) := by ring
      have hexp2 : (k + 1) * dim = k * dim + dim := by ring
      have hhead : n / (k + 1) ≤ dim := by
        by_contra hcon
        push_neg at hcon
        have hmul : (k + 1) * (dim + 1) ≤ (k + 1) * (n / (k + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
        have hexp : (k + 1) * (dim + 1) = (k + 1) * dim + k + 1 := by ring
        omega
      simp only [chunkSizes, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hhead
      · refine chunkSizes_le k (n - n / (k + 1)) dim ?_ s hs
        have hkq : k * (n / (k + 1)) ≤ k * dim := Nat.mul_le_mul_left _ hhead
        by_cases hqd : n / (k + 1) < dim
        · have hstep : k * (n / (k + 1) + 1) ≤ k * dim := Nat.mul_le_mul_left _ (by omega)
          have hexp3 : k * (n / (k + 1) + 1) = k * (n / (k + 1)) + k := by ring
          omega
        · have hqe : n / (k + 1) = dim := by omega
          rw [hqe] at hdm hexp1 hkq ⊢
          omega

/-! ## Residual

What this file leaves outside, in the same place `Shift.lean` and `Compare.lean` leave theirs.

* **Booleanity.** `Separates` is about `List Bool`; that the wires carry bits is the 284,703
  `is_boolean` assertions, and the bridge from a field element to the `Bool` it encodes belongs
  with them.
* **`pseudo_basis` is the model's `c`.** That GF(2¹²⁸)'s `1 <<< i` is `α ^ i`, and that 𝔽ₚ's
  `2 ^ i mod p` is `(2 : F) ^ i`, are read off `compile/algebra/{gf2_128,fp}.rs` — one line each,
  but read rather than proved.
* **`IsGen α`.** `separates_gf128` takes it; `GF128/Irred.lean` proves it for the concrete model,
  from irreducibility of `x¹²⁸ + x⁷ + x² + x + 1`.
-/

end ChunkEq
end MDoc
