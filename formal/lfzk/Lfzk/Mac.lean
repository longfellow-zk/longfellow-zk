import Mathlib
import Sumcheck.Counting

/-!
# The two-field MAC

The information-theoretic MAC of §3.4 of the paper, which is what ties two Longfellow arguments
over two *different* fields to one common witness.  Nothing here is about a protocol: this file is
one keyed function on `Fin nblk → Fmac` and the two facts about it that Theorem 9 uses.

## The construction

The paper writes `MAC_{a,b}(x) = ax + b` for a single value `x`. This file models the
multi-block additive-blind form used by the Rust v8 construction:

```
tag j = a * msg j + b j          -- `rust/circuits/mac/src/concrete.rs:41`
```

**one multiplier shared across the blocks, one blind per block.**  `mac_av : u128` and
`mac_ap : [u128; 2]` in `ConcreteGiven` (`concrete.rs:16`); the circuits assert
`tag[j] ⊕ mac_ap[j] = mac_av · msg[j]` for each `j`, bit-sliced over the prime field
(`mac/src/circuit.rs:46`) and natively over `GF(2^128)` (`mac_gf128/src/circuit.rs:47`).

Sharing the multiplier is what makes the collision bound exact.  A polynomial hash
`∑ x_j a^j + b` would pay a degree factor `nblk/|Fmac|`; here a collision in *any* block forces
`a = 0` outright **when both sides use the same blind**. With separate fixed blinds, a collision
instead pins `a` to at most one value (`macTag_collision_card_le_one`). The bound for a fixed pair
of messages and blinds is `1/|Fmac|` for **every** `nblk` — `2^-128` at the deployed field size.
Giving each block its own blind is what makes the hiding step *perfect*: the tag is a
translate of the blind (`macBlindEquiv`), so it is uniform and independent of the message.

**Deployment boundary:** the Rust v8 circuits have separate private `mac_ap` witnesses. The honest
prover uses equal blinds, but verifier acceptance does not establish their equality by itself.
The existing `Lfzk.TwoField` composition assumes a shared blind and uses the zero-multiplier bad
event. Instantiating it for Rust requires a different composition argument for fixed pre-challenge
candidate lists and their possibly different blinds; the separate-blind lemma here does not yet
discharge that obligation.

The v7 compatibility path instead uses `(a + ap j) * msg j`, as do the C++ MAC circuits.
For soundness this is affine in `a` with offset `ap j * msg j`, covered by
`shiftedMultiplier_collision_card_le_one` for a fixed pair. Its hiding property differs:
at a zero message block the tag is always zero, so `macBlindEquiv` does not establish perfect
hiding for that path.

Both halves are load-bearing and neither can be dropped:

* drop the per-block blinds (the paper's footnote 5, `MAC_a(x) = a·x`) and for `nblk ≥ 2` the tag
  lies on a line — `tag 1 / tag 0 = msg 1 / msg 0` is a function of the witness, so the hiding step
  is not perfect and not even close.  The footnote is stated for a single value and is correct
  there; `Lfzk.Example` carries the leak at `nblk = 2` as a theorem;
* give each block its own multiplier and the collision bound is unchanged but the key grows.

## What is proved

| | |
|---|---|
| `macTag_collision` | with the same blind on both sides, a collision at *any* block forces the multiplier to be `0` |
| `macTag_collision_card_le_one` | with separate fixed blinds and unequal fixed messages, at most one multiplier collides |
| `macKeyBad_eq_singleton`, `macKeyBad_card` | exactly one verifier coin kills the multiplier — the bound is `1/\|Fmac\|` and it is **tight** |
| `macKeyBad_split_card` | the count over `D × Fmac`, in `Sumcheck.pairs_card_le`'s idiom |
| `macBlindEquiv` | the tag as a translate of the prover's blind: an `Equiv`, so hiding costs `0` |
| `packBits_injective` | §3.2's basis injection is injective from `GF(2)`-independence |

`Lfzk.TwoField` consumes the first three; `Lfzk.TwoFieldZk` consumes `macBlindEquiv`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Classical

namespace Lfzk.Mac

variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/--
**The MAC.**  `rust/circuits/mac/src/concrete.rs:41`: one multiplier `a` for every block, one
blind `b j` per block.
-/
def macTag (a : Fmac) (b msg : Fin nblk → Fmac) : Fin nblk → Fmac :=
  fun j => a * msg j + b j

@[simp] lemma macTag_apply (a : Fmac) (b msg : Fin nblk → Fmac) (j : Fin nblk) :
    macTag a b msg j = a * msg j + b j := rfl

/-! ## Soundness: a collision forces the multiplier to vanish -/

/--
**The collision fact.**

Two *different* messages with the same tag force `a = 0`, and the argument is one line: at a block
where the messages differ, the blinds cancel and `a * (msg j - msg' j) = 0`.

No union bound over blocks, no degree factor, and the statement is uniform in `nblk` — this is
exactly what sharing the multiplier buys.  It is also independent of `b`, which is why the hiding
blind costs nothing on the soundness side.
-/
theorem macTag_collision {a : Fmac} {b msg msg' : Fin nblk → Fmac}
    (hne : msg ≠ msg') (hcol : macTag a b msg = macTag a b msg') : a = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have h : a * msg j + b j = a * msg' j + b j := congrFun hcol j
  have hd : msg j - msg' j ≠ 0 := sub_ne_zero.mpr hj
  have hz : a * (msg j - msg' j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hz with h1 | h1
  · exact h1
  · exact absurd h1 hd

/--
The contrapositive, in the form the composed extractor uses: at a nonzero multiplier, equal tags
mean equal messages.
-/
theorem macTag_injective_of_ne_zero {a : Fmac} (ha : a ≠ 0) (b : Fin nblk → Fmac) :
    Function.Injective (macTag a b) := fun _ _ h => by
  by_contra hne
  exact ha (macTag_collision hne h)

/-- With separate blinds, two fixed unequal messages can collide at only one multiplier.
Unlike `macTag_collision`, that multiplier need not be zero. The messages and both blinds must
be fixed independently of the sampled multiplier when using this lemma probabilistically. -/
theorem macTag_collision_unique {b b' msg msg' : Fin nblk → Fmac}
    (hne : msg ≠ msg') {a a' : Fmac}
    (h : macTag a b msg = macTag a b' msg')
    (h' : macTag a' b msg = macTag a' b' msg') : a = a' := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have h1 : a * msg j + b j = a * msg' j + b' j := congrFun h j
  have h2 : a' * msg j + b j = a' * msg' j + b' j := congrFun h' j
  have hz : (a - a') * (msg j - msg' j) = 0 := by linear_combination h1 - h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hj))

/-- The separate-blind collision probability is at most `1/|Fmac|` for each fixed pair.
This is not yet a bound for adaptively selected members of two candidate lists. -/
theorem macTag_collision_card_le_one [Fintype Fmac] [DecidableEq Fmac]
    (b b' msg msg' : Fin nblk → Fmac) (hne : msg ≠ msg') :
    (univ.filter fun a => macTag a b msg = macTag a b' msg').card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha a' ha'
  exact macTag_collision_unique hne (mem_filter.mp ha).2 (mem_filter.mp ha').2

/-- The v7 formula has the same fixed-pair soundness bound: absorb each committed
`ap j * msg j` into an affine offset. This does not equate its hiding property with v8's. -/
theorem shiftedMultiplier_collision_card_le_one [Fintype Fmac] [DecidableEq Fmac]
    (ap ap' msg msg' : Fin nblk → Fmac) (hne : msg ≠ msg') :
    (univ.filter fun a : Fmac =>
      (fun j => (a + ap j) * msg j) = (fun j => (a + ap' j) * msg' j)).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha a' ha'
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have h1 : (a + ap j) * msg j = (a + ap' j) * msg' j :=
    congrFun (mem_filter.mp ha).2 j
  have h2 : (a' + ap j) * msg j = (a' + ap' j) * msg' j :=
    congrFun (mem_filter.mp ha').2 j
  have hz : (a - a') * (msg j - msg' j) = 0 := by linear_combination h1 - h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hj))

/-! ### The bad set of verifier coins

The key is jointly sampled: the prover commits `a_p` and the verifier then sends `a_v`, so the
multiplier is `a_p + a_v`.  The bad event of `macTag_collision` is `a_p + a_v = 0`, and the whole
probabilistic content of the two-field step is that this is one coin out of `|Fmac|`.

Under the shared-blind premise, the bad event does not mention the messages, so no binding
hypothesis on either side's extractor is needed — see `Lfzk.TwoField`. This simplification does
not apply to the Rust circuits' separate private blinds without an additional argument. -/

/-- The verifier coins that kill the multiplier, at a fixed prover share. -/
def MacKeyBad (ap av : Fmac) : Prop := ap + av = 0

section Counting

variable [Fintype Fmac] [DecidableEq Fmac]

/-- **Exactly one** verifier coin is bad, namely `-a_p`. -/
theorem macKeyBad_eq_singleton (ap : Fmac) :
    (univ.filter fun av : Fmac => MacKeyBad ap av) = {-ap} := by
  ext av
  simp only [mem_filter, mem_univ, true_and, mem_singleton, MacKeyBad]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

/-- The bound is `1`, and it is an equality — so `1/|Fmac|` is tight, not an over-estimate. -/
theorem macKeyBad_card (ap : Fmac) :
    (univ.filter fun av : Fmac => MacKeyBad ap av).card = 1 := by
  rw [macKeyBad_eq_singleton, card_singleton]

theorem macKeyBad_card_le_one (ap : Fmac) :
    (univ.filter fun av : Fmac => MacKeyBad ap av).card ≤ 1 :=
  le_of_eq (macKeyBad_card ap)

/--
**The count over the whole sample space.**

`Ω = D × Fmac`: everything the prover decided before the key challenge, times the challenge.  The
prover share `a_p` is a function of the prefix, the challenge is free, so the bad set has exactly
one point per prefix — a `1/|Fmac|` fraction.

This is `Sumcheck.pairs_card_le`, the same splitting idiom `Lfzk.Types.alpha_bad_card` uses for the
input-binding challenge.
-/
theorem macKeyBad_split_card {D : Type} [Fintype D] (aP : D → Fmac) :
    (univ.filter fun p : D × Fmac => MacKeyBad (aP p.1) p.2).card ≤ Fintype.card D :=
  Sumcheck.pairs_card_le (fun d av => MacKeyBad (aP d) av)
    (fun d => macKeyBad_card_le_one (aP d))

end Counting

/-! ## Zero knowledge: the tag is a translate of the prover's blind -/

/--
**The hiding bijection.**

At a fixed multiplier, message and verifier blind, `b_p ↦ macTag a (b_p + b_v) msg` is translation
by `fun j => a * msg j + b_v j`.  So the tag is uniformly distributed and *independent of the
message*, and the paper's last hybrid — "the mac value `m` is randomly sampled instead of computed
using `w`" — costs exactly `0` rather than being statistically close.

This is the `Lfzk.ZkHiding.blindEquiv` argument again, at the MAC instead of at the pad, and it is
why the two-field composition adds nothing to the zero-knowledge error.
-/
def macBlindEquiv (a : Fmac) (bv msg : Fin nblk → Fmac) :
    (Fin nblk → Fmac) ≃ (Fin nblk → Fmac) where
  toFun bp := macTag a (bp + bv) msg
  invFun t := fun j => t j - (a * msg j + bv j)
  left_inv bp := by funext j; simp only [macTag_apply, Pi.add_apply]; ring
  right_inv t := by funext j; simp only [macTag_apply, Pi.add_apply]; ring

@[simp] lemma macBlindEquiv_apply (a : Fmac) (bv msg bp : Fin nblk → Fmac) :
    macBlindEquiv a bv msg bp = macTag a (bp + bv) msg := rfl

/-- Stated as surjectivity: *every* tag is produced by some prover blind.  This is the form the
hybrid argument reads it in — the simulator's uniform tag is in the image. -/
theorem macTag_surjective_in_blind (a : Fmac) (bv msg : Fin nblk → Fmac) :
    Function.Surjective (fun bp => macTag a (bp + bv) msg) :=
  (macBlindEquiv a bv msg).surjective

/-! ## The common witness is bits

In both circuits the shared value is carried as 256 *bit* wires (`Bitvec<L, 256>`), and each side
packs them into `Fmac` its own way — `bv.as_eltw_field` natively, or the bit-sliced multiplier over
the prime field.  §3.2's injection `F(j) = ∑ jᵢ βᵢ` is that packing.

The core theorems of `Lfzk.TwoField` are stated at the *packed* level, where no injectivity is
needed.  This section is what upgrades their conclusion from "the two sides packed to the same
`Fmac` elements" to "the two sides committed the same bits", and it is the only place the basis
appears. -/

/-- §3.2's injection: read the bits as coordinates in the basis `β`. -/
def packBits {k : ℕ} (β : Fin k → Fmac) (bits : Fin k → Bool) : Fmac :=
  ∑ i, if bits i then β i else 0

/-- `β` is `GF(2)`-independent: no nonempty sub-family sums to zero.  Stated as a condition on
`Finset` sums rather than through `Module (ZMod 2)`, which would need the characteristic in the
type class and buys nothing here. -/
def SubsetIndependent {k : ℕ} (β : Fin k → Fmac) : Prop :=
  ∀ s : Finset (Fin k), ∑ i ∈ s, β i = 0 → s = ∅

/-- In characteristic 2 every element is its own negative. -/
private lemma neg_eq_self (h2 : (2 : Fmac) = 0) (x : Fmac) : -x = x := by
  have hxx : x + x = 0 := by linear_combination x * h2
  linear_combination -hxx

/--
**The packing is injective.**

Two bit-strings with the same packing differ on a set whose basis elements sum to zero — in
characteristic 2, because each element on which they agree contributes `βᵢ - βᵢ = 0` and each
element on which they differ contributes `±βᵢ = βᵢ`.  `GF(2)`-independence then forces that set to
be empty.

For `GF(2)[x]/(Q(x))` with the monomial basis this hypothesis holds, which is the deployed case
(`Q(x) = x^128 + x^7 + x^2 + x + 1`, §3.3).
-/
theorem packBits_injective {k : ℕ} (β : Fin k → Fmac) (h2 : (2 : Fmac) = 0)
    (hindep : SubsetIndependent β) : Function.Injective (packBits β) := by
  intro bits bits' heq
  by_contra hne
  have hsum : ∑ i ∈ univ.filter (fun i => bits i ≠ bits' i), β i = 0 := by
    rw [sum_filter]
    have hterm : ∀ i : Fin k, (if bits i ≠ bits' i then β i else 0)
        = (if bits i then β i else 0) - (if bits' i then β i else 0) := by
      intro i
      rcases Bool.eq_false_or_eq_true (bits i) with h | h <;>
        rcases Bool.eq_false_or_eq_true (bits' i) with h' | h' <;>
        simp [h, h', neg_eq_self h2]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq
  have hempty := hindep _ hsum
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have : i ∈ univ.filter (fun i => bits i ≠ bits' i) := by
    simp only [mem_filter, mem_univ, true_and]; exact hi
  rw [hempty] at this
  simp at this

/-- Non-vacuity: `SubsetIndependent` is satisfiable.  A one-element family at a nonzero value. -/
theorem subsetIndependent_single (c : Fmac) (hc : c ≠ 0) :
    SubsetIndependent (fun _ : Fin 1 => c) := by
  intro s hs
  rcases Finset.eq_empty_or_nonempty s with h | h
  · exact h
  · obtain ⟨i, hi⟩ := h
    have hsub : s = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hi, fun x _ => Subsingleton.elim x i⟩
    rw [hsub, Finset.sum_singleton] at hs
    exact absurd hs hc

end Lfzk.Mac
