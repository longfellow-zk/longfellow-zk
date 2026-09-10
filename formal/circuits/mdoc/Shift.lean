/-
# The barrel shifter

`Assertions.lean` writes every offset clause over `window bs off n` — "the `n` bytes of `bs`
starting at `off`, zero past the end". The circuit does not have a `window`; it has
`routing::shift_bitvec`, a log-depth network of one-hot muxes. This file proves they agree, which
discharges the first of the four gadget obligations `meaning` names.

## The algorithm

`generic_shift` (`rust/circuits/routing/src/circuit.rs`) walks the bits of `amount` from the top
down, in groups. Each round consumes `consumed` bits at positions `l … l + consumed`, builds a
one-hot selector over their value `sel` (`amount_selector` via `relint`/`eqb`), and calls

```rust
really_shift(mux, &selector, n, k, &mut tmp, 1 << l, default)
```

which overwrites `tmp[i]` with `extend(aa, default, i + sel · 2^l)` for every `i` below
`min(n, k + 2^l)`, leaving the rest of `tmp` alone. After the last round it returns
`(0..k).map(|i| if i < n { tmp[i] } else { default })`.

## Why the truncation is the interesting part

`really_shift` stops at `min(n, k + shift)`, so entries above that keep values from the previous
round — and the next round *reads* entries above its own limit. The two bounds are exactly tight
and it is worth seeing why. Round `r + 1` reads at most

```
    (k + 2^{l_{r+1}} - 1) + (2^{c_{r+1}} - 1) · 2^{l_{r+1}}
  = k + 2^{l_{r+1} + c_{r+1}} - 1
  = k + 2^{l_r} - 1
```

using `l_{r+1} + c_{r+1} = l_r`, and round `r` wrote everything below `k + 2^{l_r}`. One index of
slack. That is why `Invariant` below is stated at `min n (k + 2 ^ hi)` rather than at `n`: a
weaker invariant would not survive the step, and a stronger one is false.

## What is modelled and what is not

The buffer is a function `Nat → α` and the selector is `amount / 2 ^ l % 2 ^ c` — that is, the
selector's *value*, not its one-hot encoding. Two things therefore stay outside:

* that `amount_selector` really is one-hot at that value, which is `eqb` plus booleanity;
* that `one_hot_mux` really returns the selected entry.

Both are single-gate facts about `arithmetic.rs`, and neither depends on the routing structure
that this file is about.
-/

import Mathlib
import mdoc.Spec
import mdoc.Assertions

/-! `Spec.lean` is deliberately Mathlib-free so that it stays cheap to `decide` against a golden
vector. This file is proof-only and nothing imports it, so it takes Mathlib for `ring` and the
`Nat` division lemmas. -/

namespace MDoc
namespace Shift

variable {α : Type}

/-! ## The model -/

/-- `extend` from `circuit.rs`: a read outside the buffer gives the fill value. -/
def ext (n : Nat) (d : α) (t : Nat → α) (i : Nat) : α := if i < n then t i else d

/-- One `really_shift` round. Indices below `min n (k + 2 ^ l)` take the entry `sel · 2 ^ l`
    further along; the rest are untouched, which is the truncation the invariant has to carry. -/
def round (n k : Nat) (d : α) (l sel : Nat) (t : Nat → α) : Nat → α :=
  fun i => if i < min n (k + 2 ^ l) then ext n d t (i + sel * 2 ^ l) else t i

/-- The rounds, most significant bit-group first. A schedule entry `(l, c)` is the round that
    consumes bits `l … l + c` and shifts by `2 ^ l`. -/
def shiftBy (n k : Nat) (d : α) (amount : Nat) : List (Nat × Nat) → (Nat → α) → (Nat → α)
  | [], t => t
  | (l, c) :: rs, t => shiftBy n k d amount rs (round n k d l (amount / 2 ^ l % 2 ^ c) t)

/-- `generic_shift`'s return: `k` entries, with anything past the buffer filled. -/
def output (n k : Nat) (d : α) (amount : Nat) (rs : List (Nat × Nat)) (a : Nat → α) (i : Nat) :
    α :=
  if i < n then shiftBy n k d amount rs a i else d

/-- The schedule covers bit positions `[0, hi)` in decreasing groups, with no gap and no overlap.
    This is the only property of the round splitting the proof uses, so the `div_ceil` arithmetic
    in `generic_shift`'s loop is confined to `chains_schedule` below. -/
def Chains : Nat → List (Nat × Nat) → Prop
  | hi, [] => hi = 0
  | hi, (l, c) :: rs => l + c = hi ∧ Chains l rs

/-- What holds of the working buffer between rounds: everything below the current limit already
    reads through the bits consumed so far. -/
def Invariant (n k : Nat) (d : α) (a t : Nat → α) (amount hi : Nat) : Prop :=
  ∀ i, i < min n (k + 2 ^ hi) → t i = ext n d a (i + amount / 2 ^ hi * 2 ^ hi)

/-! ## The step

The one piece of arithmetic: splitting `amount` at bit `l` and again at bit `l + c` recombines. -/

private theorem split_pow (amount l c : Nat) :
    amount / 2 ^ l % 2 ^ c * 2 ^ l + amount / 2 ^ (l + c) * 2 ^ (l + c)
      = amount / 2 ^ l * 2 ^ l := by
  have hdd : amount / 2 ^ (l + c) = amount / 2 ^ l / 2 ^ c := by
    rw [pow_add, Nat.div_div_eq_div_mul]
  have hp : (2 : Nat) ^ (l + c) = 2 ^ c * 2 ^ l := by rw [pow_add]; ring
  have hmd := Nat.mod_add_div (amount / 2 ^ l) (2 ^ c)
  rw [hdd, hp]
  calc amount / 2 ^ l % 2 ^ c * 2 ^ l + amount / 2 ^ l / 2 ^ c * (2 ^ c * 2 ^ l)
      = (amount / 2 ^ l % 2 ^ c + 2 ^ c * (amount / 2 ^ l / 2 ^ c)) * 2 ^ l := by ring
    _ = amount / 2 ^ l * 2 ^ l := by rw [hmd]

/-- One round advances the invariant from level `l + c` to level `l`. -/
theorem invariant_round (n k : Nat) (d : α) (a t : Nat → α) (amount l c : Nat)
    (h : Invariant n k d a t amount (l + c)) :
    Invariant n k d a (round n k d l (amount / 2 ^ l % 2 ^ c) t) amount l := by
  intro i hi
  have hpos : 0 < (2 : Nat) ^ l := Nat.two_pow_pos l
  simp only [round, if_pos hi]
  set s := amount / 2 ^ l % 2 ^ c with hs
  -- the read index stays inside the *previous* round's limit, with exactly one to spare
  have hsle : s ≤ 2 ^ c - 1 := by
    have : s < 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos c)
    omega
  have hbound : i + s * 2 ^ l < k + 2 ^ (l + c) := by
    have h1 : i < k + 2 ^ l := by omega
    have h2 : s * 2 ^ l ≤ (2 ^ c - 1) * 2 ^ l := Nat.mul_le_mul_right _ hsle
    have h3 : (2 ^ c - 1) * 2 ^ l = 2 ^ (l + c) - 2 ^ l := by
      have hc : 0 < (2 : Nat) ^ c := Nat.two_pow_pos c
      have hx : (2 : Nat) ^ (l + c) = 2 ^ c * 2 ^ l := by rw [pow_add]; ring
      rw [hx, Nat.sub_mul, one_mul]
    have h4 : (2 : Nat) ^ l ≤ 2 ^ (l + c) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  by_cases hin : i + s * 2 ^ l < n
  · -- inside the buffer: the invariant applies to the entry being read
    have hlt : i + s * 2 ^ l < min n (k + 2 ^ (l + c)) := by omega
    have hidx : i + s * 2 ^ l + amount / 2 ^ (l + c) * 2 ^ (l + c)
        = i + amount / 2 ^ l * 2 ^ l := by rw [Nat.add_assoc, split_pow]
    have e1 : ext n d t (i + s * 2 ^ l) = t (i + s * 2 ^ l) := if_pos hin
    rw [e1, h _ hlt, hidx]
  · -- outside: both sides are the fill value
    have : ¬ (i + s * 2 ^ l + amount / 2 ^ (l + c) * 2 ^ (l + c) < n) := by omega
    simp only [ext, if_neg hin, if_neg (by
      have hrw : i + amount / 2 ^ l * 2 ^ l
          = i + s * 2 ^ l + amount / 2 ^ (l + c) * 2 ^ (l + c) := by
        rw [Nat.add_assoc, split_pow]
      rw [hrw]; omega : ¬ (i + amount / 2 ^ l * 2 ^ l < n))]

/-! ## The theorem -/

/-- The rounds carry the invariant all the way down to level 0. -/
theorem shiftBy_invariant (n k : Nat) (d : α) (a : Nat → α) (amount : Nat) :
    ∀ (rs : List (Nat × Nat)) (hi : Nat) (t : Nat → α),
      Chains hi rs → Invariant n k d a t amount hi →
      Invariant n k d a (shiftBy n k d amount rs t) amount 0 := by
  intro rs
  induction rs with
  | nil => intro hi t hch hinv; cases hch; exact hinv
  | cons r rs ih =>
      obtain ⟨l, c⟩ := r
      intro hi t hch hinv
      obtain ⟨hlc, hrest⟩ := hch
      subst hlc
      exact ih l _ hrest (invariant_round n k d a t amount l c hinv)

/-- **The barrel shifter reads `a` at `i + amount`.** For every output index the circuit
    produces, `shift_bitvec` returns the buffer entry `amount` further along, or the fill value
    when that is past the end.

    `hamt` is the bit width the amount wire carries — 16 for the MSO offsets, 10 for the
    attribute ones, 2 for the field-locator permutation. -/
theorem output_spec (n k : Nat) (d : α) (a : Nat → α) (amount hi : Nat)
    (hamt : amount < 2 ^ hi) (rs : List (Nat × Nat)) (hch : Chains hi rs) :
    ∀ i, i < k → output n k d amount rs a i = ext n d a (i + amount) := by
  have hbase : Invariant n k d a a amount hi := by
    intro i hi'
    have h0 : amount / 2 ^ hi = 0 := Nat.div_eq_of_lt hamt
    have hlt : i < n := by omega
    simp [ext, h0, hlt]
  have hfin := shiftBy_invariant n k d a amount rs hi a hch hbase
  intro i hik
  by_cases hin : i < n
  · have : i < min n (k + 2 ^ 0) := by simp only [lt_min_iff]; exact ⟨hin, by omega⟩
    simpa [output, hin] using hfin i this
  · simp [output, hin, ext, show ¬ (i + amount < n) by omega]

/-! ## The schedule `generic_shift` actually uses

```rust
let mut l = logn;
let mut target_nrounds = logn.div_ceil(unroll);
while target_nrounds > 0 {
    let consumed = l.div_ceil(target_nrounds);
    l -= consumed;
    …                          // round (l, consumed)
    target_nrounds -= 1;
}
```
-/

/-- The loop above, as a list. `t` is `target_nrounds`. -/
def schedule : Nat → Nat → List (Nat × Nat)
  | _, 0 => []
  | l, t + 1 => ((l - (l + t) / (t + 1)), (l + t) / (t + 1)) :: schedule (l - (l + t) / (t + 1)) t

/-- A ceiling-sized group is never larger than what is left. -/
private theorem ceil_le (l t : Nat) : (l + t) / (t + 1) ≤ l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simpa using Nat.div_eq_of_lt (by omega : t < t + 1)
  · by_contra hcon
    push_neg at hcon
    have h1 : (t + 1) * (l + 1) ≤ (t + 1) * ((l + t) / (t + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (l + t) / (t + 1) * (t + 1) ≤ l + t := Nat.div_mul_le_self _ _
    have h3 : (t + 1) * ((l + t) / (t + 1)) = (l + t) / (t + 1) * (t + 1) := by ring
    have h4 : (t + 1) * (l + 1) = t * l + t + l + 1 := by ring
    omega

/-- **The schedule chains.** `generic_shift` asserts `unroll > 0`, so `target_nrounds` is positive
    whenever there is a bit to consume, and the loop lands exactly on `l = 0`. `output_spec`
    therefore applies to the circuit's own round splitting, for every `unroll` and every amount
    width. -/
theorem chains_schedule : ∀ (t : Nat), 0 < t → ∀ l : Nat, Chains l (schedule l t)
  | 1, _, l => by
      have h : (l + 0) / (0 + 1) = l := by simp
      simp only [schedule, Chains, h]
      exact ⟨by omega, by simp [schedule, Chains]⟩
  | t + 2, _, l => by
      simp only [schedule, Chains]
      exact ⟨by have := ceil_le l (t + 1); omega,
        chains_schedule (t + 1) (by omega) _⟩

/-- The schedule for an empty amount is empty. -/
theorem chains_schedule_zero : Chains 0 (schedule 0 0) := by simp [schedule, Chains]

/-! ## The circuit's own call sites

`chains_schedule` says every positive round count works, which is easy to believe and therefore
easy to get wrong: if `schedule` did not match `generic_shift`'s loop, it would still chain. So
the schedules are also pinned by value against a hand-trace of the Rust, at the five widths and
`unroll`s the mdoc circuits actually use.

`target_nrounds` is `logn.div_ceil(unroll)`, so the second argument below is that, not `unroll`. -/

/-- The MSO offsets are 16-bit, and `shift_preimage` is called with `unroll` 3, 4 and 7. -/
theorem schedule_mso :
    schedule 16 6 = [(13, 3), (10, 3), (7, 3), (4, 3), (2, 2), (0, 2)] ∧   -- unroll 3
    schedule 16 4 = [(12, 4), (8, 4), (4, 4), (0, 4)] ∧                    -- unroll 4
    schedule 16 3 = [(10, 6), (5, 5), (0, 5)] :=                           -- unroll 7
  ⟨rfl, rfl, rfl⟩

/-- An attribute slot offset is 10-bit, shifted with `unroll` 3. -/
theorem schedule_attr : schedule 10 4 = [(7, 3), (4, 3), (2, 2), (0, 2)] := rfl

/-- `slot_offset_and_len` routes a 2-bit permutation entry with `unroll` 1. -/
theorem schedule_locator : schedule 2 2 = [(1, 1), (0, 1)] := rfl

/-- Every one of them chains, so `output_spec` applies at each call site. -/
theorem chains_call_sites :
    Chains 16 (schedule 16 6) ∧ Chains 16 (schedule 16 4) ∧ Chains 16 (schedule 16 3) ∧
    Chains 10 (schedule 10 4) ∧ Chains 2 (schedule 2 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [schedule, Chains]

/-! ## Landing on `window`

`Spec.lean`'s vocabulary, so the gadget obligation is discharged in the form `Assertions.lean`
uses it. -/

/-- On a byte buffer with fill `0`, `ext` is just `byteAt`: a `List Nat` already reads as `0` past
    its end, which is why `Spec.lean` could be written with `getD` and no side conditions. -/
theorem ext_byteAt (bs : List Nat) (i : Nat) :
    ext bs.length 0 (fun j => byteAt bs j) i = byteAt bs i := by
  simp only [ext, byteAt]
  split
  · rfl
  · rename_i h
    rw [List.getD_eq_default]
    omega

/-- The pointwise form, which is what a clause reads: entry `i` of the shifted window is the
    buffer's byte at `off + i`. `Assertions.Reads` is exactly this, quantified. -/
theorem output_byteAt (bs : List Nat) (k off hi i : Nat) (hamt : off < 2 ^ hi)
    (rs : List (Nat × Nat)) (hch : Chains hi rs) (hik : i < k) :
    output bs.length k 0 off rs (fun j => byteAt bs j) i = byteAt bs (off + i) := by
  rw [output_spec bs.length k 0 (fun j => byteAt bs j) off hi hamt rs hch i hik, ext_byteAt,
    Nat.add_comm]

/-- **The obligation, discharged.** `shift_bitvec off k bs` is `window bs off k`. -/
theorem shift_is_window (bs : List Nat) (k off hi : Nat) (hamt : off < 2 ^ hi)
    (rs : List (Nat × Nat)) (hch : Chains hi rs) :
    (List.range k).map (output bs.length k 0 off rs (fun j => byteAt bs j))
      = window bs off k := by
  simp only [window]
  refine List.map_congr_left ?_
  intro i hi'
  have hik : i < k := by simpa using List.mem_range.mp hi'
  rw [output_spec bs.length k 0 (fun j => byteAt bs j) off hi hamt rs hch i hik, ext_byteAt,
    Nat.add_comm]

/-! ## Discharged

`Assertions.meaning` takes `Reads rd 16` as a hypothesis and uses it at every offset clause. This
is what supplies it, so the barrel-shifter lemma is load-bearing rather than merely true: delete
`output_byteAt` and `meaning_of_gates` stops typechecking. -/

/-- The circuit's reading of a buffer at a prover-supplied offset: entry `i` of the window the
    routing network produced. -/
def gateRead (rs : List (Nat × Nat)) : Rd :=
  fun bs k off i => output bs.length k 0 off rs (fun j => byteAt bs j) i

/-- **The shifter obligation, discharged**, for any schedule that chains — which by
    `chains_call_sites` is every one the mdoc circuits use. -/
theorem reads_gateRead (hi : Nat) (rs : List (Nat × Nat)) (hch : Chains hi rs) :
    Reads (gateRead rs) hi :=
  fun bs k off i hoff hik => output_byteAt bs k off hi i hoff rs hch hik

/-- **The shifter half of `GadgetsOk`, for the circuit's own reader.** The other three fields are
    `mdoc/Gadgets.lean`'s; this is the one that lives here, so that `Shift.output_byteAt` is what
    the meaning layer rests on. -/
theorem gadgets_reads (rs : List (Nat × Nat)) (hch : Chains hashIndexBits rs)
    (g : Gadgets) (hrd : g.rd = gateRead rs) : Reads g.rd hashIndexBits := by
  rw [hrd]; exact reads_gateRead hashIndexBits rs hch

/-- **The meaning theorem over the gate-level assertion set.** `Asserted g` with `g.rd` the
    circuit's own reading — the assertions as they are made about the routing network's outputs,
    not about the buffer — and this says they still imply the specification. -/
theorem meaning_of_gates (g : Gadgets) (rs : List (Nat × Nat)) (hch : Chains hashIndexBits rs)
    (hrd : g.rd = gateRead rs) (hcmp : GadgetsOk g)
    (s : Statement) (w : Witness)
    (hwd : Widths s w)
    (hwf : WellFormed s)
    (hsha : sha256 w.preimage w.nblocks = w.e)
    (hshaAttr : ∀ i, i < s.attrId.length →
      sha256 (w.attrs.getD i default).preimage attrShaBlocks
        = window w.preimage ((w.attrs.getD i default).digestOff + tag32.length) 32)
    (h : Asserted g s w) :
    ValidPresentation s :=
  meaning g s w { hcmp with reads := gadgets_reads rs hch g hrd } hwd hwf hsha hshaAttr h

end Shift
end MDoc
