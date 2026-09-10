import quadcert.Core.ConeChain
import GF128.Cone

/-!
# Reading the wrapping-sum cone's chain nodes

`Core/ConeChain.lean` evaluates a chained template to `chainVals` without unfolding a single
`getD` at the instance. `GF128/Cone.lean` says what the top of the cone means. This file is the
join: it identifies each *kind* of node the `assert_wrapping_sum_gf2` cone contains with the
algebra `GF128/Wrap.lean` is stated over.

Measured on `Gen/Sha256Gf2`, one such cone has 632 nodes in exactly three kinds, and the two
that make up the middle are handled here:

* `[(0, 0, 0), (2 + i, 0, b)]` — two terms, `1 + c₂₊ᵢ · lv b`. With `const_eq_injBasis` that is
  `injFactor α i (lv b)`, one factor of an injection. There are 134 of them.
* `[(0, a, b)]` — one term, a binary product of two earlier chain nodes. There are 208, and they
  are the product trees: the 32 factors of each injection, the six injections of `got`, and the
  `wrapPolyM` factors.

The third kind, `[(0,0,0), (2+i, 0, b₁), (2+i, b₁, b₂), (2+i, b₂, b₃)]`, is the same injection
factor applied to a bit the compiler computed rather than witnessed — `algsimp` fused `Ch`'s
`g + eg + ef` into the factor. `injFactor_fused` covers it: the shape is `injFactor α i` of
whatever polynomial the extra terms spell, so it needs no new algebra, only the observation that
the coefficient is shared.

What is still generation rather than proof: emitting the concrete `mv` for a cone and running
`coneIs` to match it. Nothing below is artifact-specific.
-/

set_option maxRecDepth 4000

namespace Sha256Gf2

open Quadcert GF128

variable {F : Type} [Field F] [CharP F 2]

/-- **An injection factor.** The `one` wire sits at leaf 0, which is why `hone` appears. -/
theorem chainNode_injFactor (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (i b : Nat) (hone : lv 0 = 1) (h0 : 0 < L) (hb : b < L)
    (hc0 : consts 0 = 1) (hci : consts (2 + i) = α ^ 2 ^ i - 1) :
    ([(0, 0, 0), (2 + i, 0, b)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = injFactor α i (lv b) := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_pos h0, if_pos hb, hone, hc0, hci,
    injFactor]
  ring

/-- **The same factor over a fused bit.** All the non-constant terms carry one coefficient, so
    whatever polynomial they spell is the bit being injected. `Ch`'s three terms are the case
    that occurs; the statement does not care how many there are. -/
theorem chainNode_injFactor_fused (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (i b₁ b₂ b₃ : Nat) (hone : lv 0 = 1) (h0 : 0 < L)
    (h1 : b₁ < L) (h2 : b₂ < L) (h3 : b₃ < L)
    (hc0 : consts 0 = 1) (hci : consts (2 + i) = α ^ 2 ^ i - 1) :
    ([(0, 0, 0), (2 + i, 0, b₁), (2 + i, b₁, b₂), (2 + i, b₂, b₃)] :
        List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = injFactor α i (lv b₁ + lv b₁ * lv b₂ + lv b₂ * lv b₃) := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_pos h0, if_pos h1, if_pos h2,
    if_pos h3, hone, hc0, hci, injFactor]
  ring

/-- **A product node.** One term with coefficient `1` over two earlier chain nodes: this is how
    every product tree in the cone is built, including `wrapPolyM`'s. -/
theorem chainNode_prod (consts lv : Nat → F) (L : Nat) (prev : List F) (a b : Nat)
    (hc0 : consts 0 = 1) (ha : L ≤ a) (hb : L ≤ b) :
    ([(0, a, b)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = prev.getD (a - L) 0 * prev.getD (b - L) 0 := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_neg (Nat.not_lt.mpr ha),
    if_neg (Nat.not_lt.mpr hb), hc0]
  ring

/-- **A `wrapPolyM` factor.** Two terms whose coefficients are `1` and a window multiplier:
    `got + cⱼ · want`. The four operands are distinct earlier chain nodes — in the measured cone
    `got = v46284 · v46548` and `want = v1721 · v46550`, so both sides are themselves products.
    In characteristic 2 the compiler's `sub` is `add`, which is why one node serves for
    `wrapPolyM`'s minus. -/
theorem chainNode_wrapFactor (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (j kj g₁ g₂ w₁ w₂ : Nat) (hc0 : consts 0 = 1)
    (hcj : consts kj = (α ^ 2 ^ 32) ^ j)
    (hg₁ : L ≤ g₁) (hg₂ : L ≤ g₂) (hw₁ : L ≤ w₁) (hw₂ : L ≤ w₂) :
    ([(0, g₁, g₂), (kj, w₁, w₂)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = prev.getD (g₁ - L) 0 * prev.getD (g₂ - L) 0
        - (α ^ 2 ^ 32) ^ j * (prev.getD (w₁ - L) 0 * prev.getD (w₂ - L) 0) := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_neg (Nat.not_lt.mpr hg₁),
    if_neg (Nat.not_lt.mpr hg₂), if_neg (Nat.not_lt.mpr hw₁), if_neg (Nat.not_lt.mpr hw₂),
    hc0, hcj]
  rw [CharTwo.sub_eq_add]
  ring

/-- **A `wrapPolyM` factor whose `got` and `want` are template leaves.** This is the shape
    `gen_gf2_wrap.py` emits: rather than following the compiler's own sharing, the generated
    template abstracts `got1, got2, want1, want2` into leaves 0…3, so the same template serves
    every instance of a class and only the map changes. -/
theorem chainNode_wrapFactor_leaf (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (j kj g₁ g₂ w₁ w₂ : Nat) (hc0 : consts 0 = 1)
    (hcj : consts kj = (α ^ 2 ^ 32) ^ j)
    (hg₁ : g₁ < L) (hg₂ : g₂ < L) (hw₁ : w₁ < L) (hw₂ : w₂ < L) :
    ([(0, g₁, g₂), (kj, w₁, w₂)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = lv g₁ * lv g₂ - (α ^ 2 ^ 32) ^ j * (lv w₁ * lv w₂) := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_pos hg₁, if_pos hg₂, if_pos hw₁,
    if_pos hw₂, hc0, hcj]
  rw [CharTwo.sub_eq_add]
  ring

/-- **The two-leg fused factor.** `σ`'s three-way xor becomes two legs at the bit positions where
    a shift kills the third, so the injected bit is `b₁ + b₂` — 624 of the 25,336 injection
    factors in the artifact. Characteristic 2 is doing the work: xor *is* addition, so unlike the
    prime-field bridge there is no `a + b - 2ab` to unfold. -/
theorem chainNode_injFactor_xor2 (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (i b₁ b₂ : Nat) (hone : lv 0 = 1) (h0 : 0 < L) (h1 : b₁ < L) (h2 : b₂ < L)
    (hc0 : consts 0 = 1) (hci : consts (2 + i) = α ^ 2 ^ i - 1) :
    ([(0, 0, 0), (2 + i, 0, b₁), (2 + i, 0, b₂)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = injFactor α i (lv b₁ + lv b₂) := by
  simp only [List.foldl_cons, List.foldl_nil, chainRead, if_pos h0, if_pos h1, if_pos h2,
    hone, hc0, hci, injFactor]
  ring

/-! ## The α-power route, for the injection cones

The wrapping-sum cone above stops at `got` and `want`, each of which is a product of two earlier
nodes. Those four nodes per cone -- 428 of them across the artifact -- are the *injection* cones,
and they are a different problem: measured, they have only 7 distinct leaf-kind mixes but **204**
distinct templates, because the compiler puts the fused 2-, 3- and 4-term factors at different
positions in each. Templating them would emit ~40,000 template nodes for ~2 instances apiece.

They do not need templating. Over GF(2^128) an injection factor on a boolean wire *is a power of
`α`* (`GF128.injFactor_eq_pow`), and a product of powers of `α` is a power of `α` whatever the
association and whatever the order. So each row is read on its own, by one of the two lemmas
below, and only the exponent survives into the next row. The census that fixes these two shapes:

| row kind | count | shape |
|---|---:|---|
| product, plain | 24,844 | `1 · a · b` |
| product, folded | 64 | `α^(Kₜ) · a · b` — one per SHA-256 round constant |
| injection factor | 21,552 | `1 + c₂₊ᵢ · (a quadratic form in bit leaves)` |

Every injection factor in the artifact has the *same* coefficient on every non-constant term, so
one lemma covers all of them: the bit being injected is whatever polynomial those terms spell,
and `hx` is the only per-row obligation. -/

/-- Folding an injection factor's non-constant terms. They share one coefficient, so the fold is
    that coefficient times the polynomial the operand pairs spell. -/
private theorem foldl_fac (consts lv : Nat → F) (L : Nat) (prev : List F) (α : F) (i : Nat)
    (hci : consts (2 + i) = α ^ 2 ^ i - 1) :
    ∀ (ts : List (Nat × Nat)), (∀ t ∈ ts, t.1 < L ∧ t.2 < L) → ∀ acc : F,
      (ts.map (fun t => ((2 + i, t.1, t.2) : Nat × Nat × Nat))).foldl
          (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
            * chainRead lv L prev t.2.2) acc
        = acc + (α ^ 2 ^ i - 1) * (ts.map (fun t => lv t.1 * lv t.2)).sum
  | [], _, acc => by simp
  | a :: l, h, acc => by
      have ha := h a (List.mem_cons_self ..)
      simp only [List.map_cons, List.foldl_cons, List.sum_cons]
      rw [foldl_fac consts lv L prev α i hci l (fun t ht => h t (List.mem_cons_of_mem _ ht)),
        chainRead, chainRead, if_pos ha.1, if_pos ha.2, hci]
      ring

/-- **An injection row, in any of the shapes the compiler emits.** `ts` is the row's operand
    pairs; `hx` names the value of the form they spell and `hn` says it is a bit. The four
    measured instantiations are a witnessed bit (`ts = [(0, b)]`), a two- or three-way xor
    (`[(0,b₁),(0,b₂)]`, `[(0,b₁),(0,b₂),(0,b₃)]`), `Ch` and `Maj` -- but the statement does not
    know which, and the artifact's many operand orderings cost nothing. -/
theorem chainNode_fac_pow (consts lv : Nat → F) (L : Nat) (prev : List F)
    (α : F) (i n : Nat) (ts : List (Nat × Nat))
    (hone : lv 0 = 1) (h0 : 0 < L) (hlt : ∀ t ∈ ts, t.1 < L ∧ t.2 < L)
    (hc0 : consts 0 = 1) (hci : consts (2 + i) = α ^ 2 ^ i - 1)
    (hx : (ts.map (fun t => lv t.1 * lv t.2)).sum = (n : F)) (hn : n = 0 ∨ n = 1) :
    (((0, 0, 0) :: ts.map (fun t => (2 + i, t.1, t.2))) : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = α ^ (2 ^ i * n) := by
  rw [List.foldl_cons, foldl_fac consts lv L prev α i hci ts hlt, hx]
  rw [← injFactor_eq_pow α i n _ rfl hn]
  simp only [chainRead, if_pos h0, hone, hc0, injFactor]
  ring

/-- **A product row.** `c · a · b` where `c = α^K`: `K = 0` for the 24,844 plain products and
    `K = Kₜ` for the 64 in which the round constant was folded in. Neither operand needs to be a
    chain node rather than a leaf, so this covers the cone's top as well as its trees. -/
theorem chainNode_prod_pow (consts lv : Nat → F) (L : Nat) (prev : List F) (α : F)
    (k a b K ea eb : Nat) (hck : consts k = α ^ K)
    (hpa : chainRead lv L prev a = α ^ ea) (hpb : chainRead lv L prev b = α ^ eb) :
    ([(k, a, b)] : List (Nat × Nat × Nat)).foldl
        (fun acc t => acc + consts t.1 * chainRead lv L prev t.2.1
          * chainRead lv L prev t.2.2) 0
      = α ^ (K + ea + eb) := by
  simp only [List.foldl_cons, List.foldl_nil, hck, hpa, hpb, zero_add, ← pow_add]

/-- The `one` wire sits at leaf 0 of every injection template, and is `α^0`. -/
theorem chainRead_one_pow (lv : Nat → F) (L : Nat) (prev : List F) (α : F)
    (hone : lv 0 = 1) (h0 : 0 < L) : chainRead lv L prev 0 = α ^ 0 := by
  simp [chainRead, h0, hone]

end Sha256Gf2
