/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import Mathlib

/-!
# The 256-bit comparison gadget

`rx_lt_order` and `nms_lt_order` assert `Boolean.assert_true` on `bv.lt`, which is
`Arithmetic::lt`: a **tree** fold (`tree_fold2`) over the 256 bit pairs, combining
`(equal, less)` states with

```
lt_base   a b            = (eqb a b, ltb a b)
lt_reduce (e₀,l₀) (e₁,l₁) = (e₀ ∧ e₁, l₁ ∨ (e₁ ∧ l₀))
```

where index 1 is the *more significant* half, since the bit arrays are least-significant-first.

Three independent properties need to be established:

1. The tree shape does not matter. `step` is associative *as a polynomial identity* — no bit
   or exclusivity hypotheses needed — so any parenthesisation of the fold agrees with the linear
   one. This is what lets the bridge ignore `tree_fold2`'s balanced splitting.
2. The fold computes the comparison. At the `Bool` level, folding `base` over two bit lists
   yields exactly `(a = b, value a < value b)`.
3. The circuit's arithmetic encodes the `Bool` operations. `eqb`, `ltb`, `andb` and
   `or_assuming_at_most_one_true` are polynomials; on 0/1 inputs they agree with the Boolean
   operations. The `or` is the delicate one: it is `x + y`, sound only because `l₁` and
   `e₁ ∧ l₀` are never both true, which `step_excl` records.
-/

namespace ECDSA2.BitLt

variable {F : Type} [Field F]

/-! ## The state monoid -/

/-- A segment's comparison state: `(equal, less)`. -/
abbrev St (F : Type) := F × F

/-- `Arithmetic::lt_base` on a pair of bits: `eqb a b = 1 - (a - b)²` (which on bits is
    `1 - a - b + 2ab`), and `ltb a b = (1 - a) * b`. -/
def base (a b : F) : St F := (1 - a - b + 2 * a * b, (1 - a) * b)

/-- `Arithmetic::lt_reduce`, with `lo` the less significant operand. The `+` is
    `or_assuming_at_most_one_true`; see `step_excl`. -/
def step (lo hi : St F) : St F := (hi.1 * lo.1, hi.2 + hi.1 * lo.2)

/-- **The tree shape is irrelevant.** `step` is associative as a polynomial identity — this needs
    no hypothesis about bits or exclusivity, so it holds for whatever splitting `tree_fold2`
    chooses. -/
theorem step_assoc (x y z : St F) : step (step x y) z = step x (step y z) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  simp only [step, Prod.mk.injEq]
  constructor <;> ring

/-- The identity: an empty segment is equal and not less. -/
theorem step_id_left (x : St F) : step (1, 0) x = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [step, Prod.mk.injEq]
  constructor <;> ring

theorem step_id_right (x : St F) : step x (1, 0) = x := by
  obtain ⟨x1, x2⟩ := x
  simp only [step, Prod.mk.injEq]
  constructor <;> ring

/-! ## From the circuit's tree to a list fold

The deployed comparator is not a linear chain: `tree_fold2` splits the 256 bit pairs into a
binary tree whose exact shape is a compiler decision. A meaning certificate reads that shape off
the DAG and reproduces it as an `STree`; this section says the shape does not matter, so the
certificate only has to get it *right*, not to justify it.

`step_assoc` does the work. Note the direction: `step lo hi` takes the less significant segment
first, so a tree flattens to the concatenation of its subtrees in that order. -/

/-- The shape the certificate reads off the DAG. Leaves index into the bit-pair list. -/
inductive STree where
  | leaf (i : Nat)
  | node (lo hi : STree)
  deriving Repr

/-- The leaves, least significant first. -/
def STree.flat : STree → List Nat
  | .leaf i => [i]
  | .node lo hi => lo.flat ++ hi.flat

/-- What the circuit computes: `step` at each node, `f` at each leaf. -/
def STree.eval (f : Nat → St F) : STree → St F
  | .leaf i => f i
  | .node lo hi => step (lo.eval f) (hi.eval f)

/-- The list fold, least significant first, with `(1, 0)` for the empty segment. -/
def foldSt (f : Nat → St F) : List Nat → St F
  | [] => (1, 0)
  | i :: is => step (f i) (foldSt f is)

theorem foldSt_append (f : Nat → St F) (a b : List Nat) :
    foldSt f (a ++ b) = step (foldSt f a) (foldSt f b) := by
  induction a with
  | nil => simp [foldSt, step_id_left]
  | cons i is ih => simp only [List.cons_append, foldSt, ih, step_assoc]

/-- **The tree flattens.** Whatever shape `tree_fold2` chose, evaluating it agrees with folding
    its leaves in order — so a meaning certificate may state its conclusion about the list. -/
theorem eval_eq_foldSt (f : Nat → St F) : ∀ t : STree, t.eval f = foldSt f t.flat
  | .leaf i => by simp [STree.eval, STree.flat, foldSt, step_id_right]
  | .node lo hi => by
      simp only [STree.eval, STree.flat, foldSt_append, eval_eq_foldSt f lo,
        eval_eq_foldSt f hi]

/-! ## The `Bool` model

The comparison itself, with no field in sight. `bval` is least-significant-first, matching
`as_eltw_unsafe`'s weighting and `to_bits`. -/

/-- Value of a bit list, least significant first. -/
def bval : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

/-- The `Bool` state of a single bit pair. -/
def bbase (a b : Bool) : Bool × Bool := (a == b, !a && b)

/-- The `Bool` reduction, `lo` less significant. -/
def bstep (lo hi : Bool × Bool) : Bool × Bool := (hi.1 && lo.1, hi.2 || (hi.1 && lo.2))

/-- Fold a pair of equal-length bit lists, least significant first. -/
def bfold : List Bool → List Bool → Bool × Bool
  | [], [] => (true, false)
  | a :: as, b :: bs => bstep (bbase a b) (bfold as bs)
  | _, _ => (true, false)

/-- Equal-length bit lists with equal values are equal. Needed by `bfold_spec` to know that an
    inequality in the high part cannot be overturned by the low bit. -/
theorem bval_inj : ∀ (a b : List Bool), a.length = b.length → bval a = bval b → a = b
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hlen, hv => by
      have hl : as.length = bs.length := by simpa using hlen
      simp only [bval] at hv
      have hpar : a = b := by
        cases a <;> cases b <;> simp_all <;> omega
      subst hpar
      have : bval as = bval bs := by
        cases a <;> (try simp only [if_true] at hv) <;> omega
      exact congrArg _ (bval_inj as bs hl this)

/-- **The fold computes the comparison.** Both components at once, since each needs the other. -/
theorem bfold_spec : ∀ (a b : List Bool), a.length = b.length →
    (bfold a b).1 = (a == b) ∧ (bfold a b).2 = decide (bval a < bval b)
  | [], [], _ => by simp [bfold, bval]
  | a :: as, b :: bs, hlen => by
      have hl : as.length = bs.length := by simpa using hlen
      obtain ⟨ih1, ih2⟩ := bfold_spec as bs hl
      simp only [bfold, bstep, bbase, ih1, ih2, bval]
      constructor
      · exact Bool.and_comm _ _
      · -- the high part decides unless the high parts are equal
        by_cases heq : as = bs
        · subst heq
          cases a <;> cases b <;> simp
        · have : (as == bs) = false := by simpa using heq
          simp only [this, Bool.false_and, Bool.or_false, decide_eq_decide]
          -- unequal high parts: `2 * bval as` and `2 * bval bs` differ by at least 2
          have hne : bval as ≠ bval bs := by
            intro hv
            exact heq (bval_inj as bs hl hv)
          rcases lt_or_gt_of_ne hne with h | h
          · have : bval as + 1 ≤ bval bs := h
            cases a <;> cases b <;> simp <;> omega
          · have : bval bs + 1 ≤ bval as := h
            cases a <;> cases b <;> simp <;> omega

/-! ## The arithmetic encoding

The circuit works in `F` with bits as `0`/`1`. `enc` is the obvious embedding, and the two
lemmas say `base` and `step` implement `bbase` and `bstep` on it. -/

/-- `Bool` as a field element. -/
def enc (b : Bool) : F := if b then 1 else 0

@[simp] theorem enc_true : enc (F := F) true = 1 := rfl
@[simp] theorem enc_false : enc (F := F) false = 0 := rfl

/-- `lt_base`'s polynomials compute `eqb` and `ltb` on bits. -/
theorem base_enc (a b : Bool) :
    base (enc (F := F) a) (enc (F := F) b) = (enc (bbase a b).1, enc (bbase a b).2) := by
  cases a <;> cases b <;>
    simp only [base, bbase, enc, Prod.mk.injEq] <;> norm_num

/-- `lt_reduce`'s polynomials compute `bstep` on bits.

    This is where `or_assuming_at_most_one_true` being `+` is discharged: on the `Bool` side the
    disjuncts are `hi.2` and `hi.1 && lo.2`, and a segment that is *less* is not *equal*, so at
    most one holds and `+` agrees with `||`. -/
theorem step_enc (lo hi : Bool × Bool) (hhi : hi.1 = true → hi.2 = false) :
    step ((enc (F := F) lo.1, enc lo.2)) ((enc hi.1, enc hi.2))
      = (enc (bstep lo hi).1, enc (bstep lo hi).2) := by
  obtain ⟨l1, l2⟩ := lo
  obtain ⟨h1, h2⟩ := hi
  cases h1 <;> cases h2 <;> cases l1 <;> cases l2 <;>
    simp_all [step, bstep, enc]

/-- The exclusivity `step_enc` needs, for the states the fold actually produces: a segment cannot
    be both equal and less. -/
theorem bfold_excl : ∀ (a b : List Bool), a.length = b.length →
    ((bfold a b).1 = true → (bfold a b).2 = false) := by
  intro a b hlen h
  obtain ⟨h1, h2⟩ := bfold_spec a b hlen
  rw [h1] at h
  have : a = b := by simpa using h
  subst this
  simp [h2]

/-- **What `rx_lt_order` buys.** If the circuit's fold reports *less*, the values compare. -/
theorem lt_of_fold (a b : List Bool) (hlen : a.length = b.length)
    (h : (bfold a b).2 = true) : bval a < bval b := by
  obtain ⟨-, h2⟩ := bfold_spec a b hlen
  rw [h2] at h
  simpa using h

/-! ## The statement a meaning certificate can discharge

`eval_eq_foldSt` turns the DAG's tree into a fold over leaf *indices*; this turns that into a
fold over the state list itself, which is what the certificate produces, and then into the
`Bool` comparison. -/

/-- `foldSt` without the indirection through indices. -/
def foldStL : List (St F) → St F
  | [] => (1, 0)
  | s :: ss => step s (foldStL ss)

theorem foldSt_eq_foldStL (f : Nat → St F) : ∀ l : List Nat, foldSt f l = foldStL (l.map f)
  | [] => rfl
  | _ :: is => by simp only [foldSt, List.map_cons, foldStL, foldSt_eq_foldStL f is]

/-- **The certificate's induction step.** A meaning lemma for `rx_lt_order` cannot expand
    `foldStL` over all 256 states -- that is a degree-256 polynomial in 256 atoms, the blowup the
    whole cone-cutting method exists to avoid. It has to mirror the circuit's tree instead, and
    this is what lets it: each `tree_fold2` node splits its segment, so one small `step` identity
    per node suffices. -/
theorem foldStL_append (a b : List (St F)) :
    foldStL (a ++ b) = step (foldStL a) (foldStL b) := by
  induction a with
  | nil => simp [foldStL, step_id_left]
  | cons s ss ih => simp only [List.cons_append, foldStL, ih, step_assoc]

@[simp] theorem foldStL_singleton (s : St F) : foldStL [s] = s := by
  simp [foldStL, step_id_right]

/-- The field-side fold of `base` states is the `Bool`-side comparison, encoded. The exclusivity
    `step_enc` needs is `bfold_excl`, so this is where "equal implies not less" is used. -/
theorem foldStL_enc : ∀ (a b : List Bool), a.length = b.length →
    foldStL ((a.zip b).map (fun q => base (enc (F := F) q.1) (enc q.2)))
      = (enc (bfold a b).1, enc (bfold a b).2)
  | [], [], _ => rfl
  | x :: xs, y :: ys, hlen => by
      have hl : xs.length = ys.length := by simpa using hlen
      -- Rewrite with the induction hypothesis *before* `base_enc`: the latter changes the shape
      -- of the mapped function and the former then no longer matches.
      rw [List.zip_cons_cons, List.map_cons, foldStL, foldStL_enc xs ys hl, base_enc, bfold]
      exact step_enc (F := F) (bbase x y) (bfold xs ys) (bfold_excl xs ys hl)

/-- **The end-to-end statement.** The certificate proves that the circuit's `rx_lt_order` wire is
    the second component of this fold; `bval a < bval b` is what the specification wants. -/
theorem lt_of_foldStL (a b : List Bool) (hlen : a.length = b.length)
    (h : (foldStL ((a.zip b).map (fun q => base (enc (F := F) q.1) (enc q.2)))).2 = 1) :
    bval a < bval b := by
  rw [foldStL_enc a b hlen] at h
  refine lt_of_fold a b hlen ?_
  cases hb : (bfold a b).2 with
  | true => rfl
  | false =>
      simp only [hb, enc_false] at h
      exact absurd h.symm one_ne_zero

end ECDSA2.BitLt
