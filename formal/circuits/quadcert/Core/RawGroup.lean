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

import quadcert.Core.Raw

/-!
# Grouping certificates for `sum_local` (no Mathlib)

Everything `Check.sum_local_of_raw` and `Check.backed_of_raw` consume, as decidable checks on
raw data. Separate from `quadcert/Raw.lean` because `Lfc3.lean` imports that one, so an edit
there rebuilds every artifact and expansion module; this file is on nothing's critical path but
the certificate modules that use it.
-/

namespace Quadcert

/-! ## A permutation witness the kernel can check

`List.isPerm` is O(n²) and hopeless on a 20k-term layer, so the witness is "the two lists have
equal sorted forms". Two things make that harder than it sounds.

**`List.mergeSort` cannot be used.** It is defined `termination_by xs => xs.length`, i.e. by
well-founded recursion, and the kernel cannot unfold `WellFounded.fix` on the accessibility
proof. `by decide` / `by rfl` over it does not reduce at any size.

**Nor can a naive top-down fuel-structural merge sort.** Writing

```
| fuel + 1, l => if l.length ≤ 1 then l
                 else merge (msort le fuel (l.take (l.length / 2)))
                            (msort le fuel (l.drop (l.length / 2))) le
```

duplicates the *unevaluated* expression `l` into three positions per level — the length test,
the take and the drop. The kernel has no hash-consing, so each copy is re-reduced
independently and the cost is 3^depth rather than n log n. Measured: 10,547 terms did not
finish in 4 minutes.

The fix is **bottom-up**: start from singletons and merge adjacent pairs. Every step consumes
its input exactly once, and `length`, `take` and `drop` never appear.

`msort_perm` holds for **every** fuel and every `le`, so both are untrusted advice: too little
fuel, or a `le` that is not a total order, leaves the lists unsorted and the generated equality
check simply fails. Nothing downstream has to know that `rawLe` orders anything.
-/

/-- Merge two lists, structural in `fuel`.

    Core's `List.merge` cannot be used: its two branches recurse on *different* arguments, so
    neither is structurally decreasing and Lean compiles it by well-founded recursion. The
    kernel then gets stuck on `[2].merge [1] le` — at length two, not at scale. Running out of
    fuel appends, which is still a permutation of `xs ++ ys`. -/
def rmerge {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if le x y then x :: rmerge le fuel xs (y :: ys)
      else y :: rmerge le fuel (x :: xs) ys

/-- Merge adjacent pairs. Structural, and each input list is used once. -/
def mergePairs {α : Type} (le : α → α → Bool) (fuel : Nat) : List (List α) → List (List α)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => rmerge le fuel a b :: mergePairs le fuel rest

/-- Bottom-up merge passes, structural in `fuel`. Running out of fuel flattens what is left,
    which is still a permutation — that is what makes the fuel untrusted. -/
def msortAux {α : Type} (le : α → α → Bool) (mfuel : Nat) : Nat → List (List α) → List α
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [l] => l
  | fuel + 1, a :: b :: rest =>
      msortAux le mfuel fuel (mergePairs le mfuel (a :: b :: rest))

/-- Merge sort the kernel can reduce. One `fuel` serves both roles: the merges need `n`, the
    passes need `ceil (log2 n)`, and `n` covers both. -/
def msort {α : Type} (le : α → α → Bool) (fuel : Nat) (l : List α) : List α :=
  msortAux le fuel fuel (l.map (fun a => [a]))

theorem rmerge_perm {α : Type} (le : α → α → Bool) :
    ∀ (fuel : Nat) (xs ys : List α), (rmerge le fuel xs ys).Perm (xs ++ ys) := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; exact List.Perm.refl _
  | succ fuel ih =>
      intro xs ys
      match xs, ys with
      | [], ys => simpa [rmerge] using List.Perm.refl ys
      | x :: xs, [] => simpa [rmerge] using List.Perm.refl (x :: xs)
      | x :: xs, y :: ys =>
          show (if le x y then x :: rmerge le fuel xs (y :: ys)
                else y :: rmerge le fuel (x :: xs) ys).Perm _
          by_cases h : le x y
          · rw [if_pos h]
            exact (ih xs (y :: ys)).cons x
          · rw [if_neg h]
            exact ((ih (x :: xs) ys).cons y).trans List.perm_middle.symm

theorem mergePairs_perm {α : Type} (le : α → α → Bool) (mfuel : Nat) :
    ∀ ls : List (List α), (mergePairs le mfuel ls).flatten.Perm ls.flatten
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: rest => by
      show (rmerge le mfuel a b :: mergePairs le mfuel rest).flatten.Perm
        ((a :: b :: rest).flatten)
      simp only [List.flatten_cons]
      refine List.Perm.trans
        ((rmerge_perm le mfuel a b).append (mergePairs_perm le mfuel rest)) ?_
      simp [List.append_assoc]

theorem msortAux_perm {α : Type} (le : α → α → Bool) (mfuel : Nat) :
    ∀ (fuel : Nat) (ls : List (List α)), (msortAux le mfuel fuel ls).Perm ls.flatten := by
  intro fuel
  induction fuel with
  | zero => intro ls; exact List.Perm.refl _
  | succ fuel ih =>
      intro ls
      match ls with
      | [] => exact List.Perm.refl _
      | [l] => show l.Perm ([l].flatten); simp
      | a :: b :: rest =>
          exact (ih (mergePairs le mfuel (a :: b :: rest))).trans
            (mergePairs_perm le mfuel (a :: b :: rest))

theorem msort_perm {α : Type} (le : α → α → Bool) (fuel : Nat) (l : List α) :
    (msort le fuel l).Perm l := by
  have hflat : ∀ l : List α, (l.map (fun a => [a])).flatten = l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  simpa [msort, hflat] using msortAux_perm le fuel fuel (l.map (fun a => [a]))

/-- Equal sorted forms give a permutation. -/
theorem perm_of_msort_eq {α : Type} (le : α → α → Bool) (fuel : Nat) (l1 l2 : List α)
    (h : msort le fuel l1 = msort le fuel l2) : l1.Perm l2 :=
  (msort_perm le fuel l1).symm.trans (h ▸ msort_perm le fuel l2)

/-- Lexicographic order on raw terms, for `msort`. Nothing is proved about it; if it were not
    a total order the generated `msort` equality would just fail to hold. -/
def rawLe (a b : RawTerm) : Bool :=
  if a.g != b.g then a.g < b.g
  else if a.h0 != b.h0 then a.h0 < b.h0
  else if a.h1 != b.h1 then a.h1 < b.h1
  else a.kIndex ≤ b.kIndex

/-! ## The per-node correspondence, on raw data

`Semantics.Realises` is field-valued, so a per-node certificate stated with it would live in a
Mathlib-importing module — 26,939 of them, at a 3.3 GB floor each. But the only field content is
`t.k = u.k`, and both sides come from the same `consts` table, so the condition is really
*equality of constant indices*. That makes the whole correspondence decidable on raw data, and
`Ingest.realises_of_raw` transports it. Third place `Raw` being field-free earns its keep. -/

/-- Raw `Realises`: layer term `t` realises the DAG sum term `(kIndex, w0, w1)` through the wire
    map. The disjunction is `canonical_term`'s operand sort (`core/proto/src/layer.rs`): the
    layer records `h0 ≤ h1`, the DAG records evaluation order, and multiplication commutes. -/
def realisesRaw (wireFn : Nat → Option (Nat × Nat)) (L : Nat) (t : RawTerm)
    (u : Nat × Nat × Nat) : Bool :=
  (t.kIndex == u.1) &&
    ((wireFn u.2.1 == some (L + 1, t.h0) && wireFn u.2.2 == some (L + 1, t.h1)) ||
     (wireFn u.2.1 == some (L + 1, t.h1) && wireFn u.2.2 == some (L + 1, t.h0)))

/-- Term-for-term, including equal lengths. -/
def realisesAll (wireFn : Nat → Option (Nat × Nat)) (L : Nat) :
    List RawTerm → List (Nat × Nat × Nat) → Bool
  | [], [] => true
  | t :: ts, u :: us => realisesRaw wireFn L t u && realisesAll wireFn L ts us
  | _, _ => false

/-- Node `nd` at index `i` agrees with its wire's group. Non-sum nodes and unwired nodes carry
    no obligation, exactly as in `ValidScheduling.sum_local`.

    Parameterised by `wireFn`, `gbound` and `groupOf` rather than by a `RawCircuit`, so a
    generated chunk module proves its own slice before the assembled circuit exists — the shape
    `ok_k` uses. -/
def groupOkWith (wireFn : Nat → Option (Nat × Nat)) (gbound : Nat → Nat)
    (groupOf : Nat → Nat → List RawTerm) (nd : RawNode) (i : Nat) : Bool :=
  match nd with
  | .sum ts =>
      match wireFn i with
      | none => true
      | some (L, g) => decide (g < gbound L) && realisesAll wireFn L (groupOf L g) ts
  | _ => true


/-! ## Reading a node without walking the list

`raw.nodes` is an append of 27 chunk literals, so reducing `nodes.getD n` allocates a cons per
element traversed and re-does it for every lookup. Measured: the value-lemma chain for a single
118-node assertion cone timed out at its 65th `getD`.

The fix is the one `wireFn` already uses — a bisection emitted alongside the data — with the
twist that the bisection is checked against the list **sequentially**: one pass over
`nodes.zipIdx`, not one lookup per node. `nodeFn_apply` then turns any single lookup into
O(log n). -/

/-- Structural equality on raw nodes, as a `Bool`. -/
def nodeEq : RawNode → RawNode → Bool
  | .input a, .input b => a == b
  | .sum a, .sum b => a == b
  | .assert0 a, .assert0 b => a == b
  | _, _ => false

theorem eq_of_nodeEq : ∀ {a b : RawNode}, nodeEq a b = true → a = b
  | .input _, .input _, h => by simpa [nodeEq] using h
  | .sum _, .sum _, h => by simpa [nodeEq] using h
  | .assert0 _, .assert0 _, h => by simpa [nodeEq] using h
  | .input _, .sum _, h => by simp [nodeEq] at h
  | .input _, .assert0 _, h => by simp [nodeEq] at h
  | .sum _, .input _, h => by simp [nodeEq] at h
  | .sum _, .assert0 _, h => by simp [nodeEq] at h
  | .assert0 _, .input _, h => by simp [nodeEq] at h
  | .assert0 _, .sum _, h => by simp [nodeEq] at h

/-- The emitted bisection agrees with the node list, at any index in range. The hypothesis is
    one sequential pass; the conclusion is a constant-time lookup. -/
theorem nodeFn_apply (r : RawCircuit) (nodeFn : Nat → RawNode)
    (h : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    {i : Nat} (hi : i < r.nodes.length) : r.nodeOf i = nodeFn i := by
  simp only [List.all_eq_true] at h
  have hmem := h (r.nodes.getD i (.input 0), i) (by
    simp only [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some])
  exact (eq_of_nodeEq hmem).symm

/-! ## `Backed`, on raw data

The soundness direction of `accepts_iff_assertions` needs only `Backed` — every named record is
carried by a real circuit constraint. (`CoversConstraints`, the converse, is what rules out
*unnamed* constraints; it is needed for the `↔`, not for `Accepts → assertions zero`.)

The only field content in `Backed` is the assertion term's coefficient being zero. In raw data a
term carries a constant *index*, so the check is parameterised by the index that denotes zero
and the spec bridge supplies `consts zeroConst = 0` — one equation, from the constant table it
already has to relate to the curve parameters. -/

/-- Raw form of `Semantics.Backed`.

    The membership test runs against `azt L` — the layer's **assertion terms only** — not against
    the layer's whole term list. That is the difference between `Σ_records (layer size)` and
    `Σ_records (assertion terms on that layer)`: on ECDSA2, 4.2M term-steps against roughly 200k,
    and the gap widens with circuit size because assertion count grows far more slowly than term
    count. `Check.backed_of_rawWith` needs only that `azt L` is a *sublist* of the layer, which a
    single `filter` equation per layer supplies.

    The membership test is `List.any` with `==` rather than `decide (_ ∈ _)`: the latter reduces
    through `List.instDecidableMemList`, building a `Decidable` value per element. -/
def backedRawWith (r : RawCircuit) (zeroConst : Nat) (azt : Nat → List RawTerm)
    (a : RawAssert) : Bool :=
  (decide (a.wireLayer < r.layers.length) &&
    (match r.wireFn a.assertedNode with
     | some p =>
        (p.1 == a.wireLayer + 1) &&
          (azt a.wireLayer).any
            (fun t => t == (⟨a.wireIndex, p.2, p.2, zeroConst⟩ : RawTerm))
     | none => false))
  || (decide (a.wireIndex < r.noutput) && (r.wireFn a.assertedNode == some (0, a.wireIndex)))

/-- The sublist property, from one `filter` equation per layer. This is what makes the whole
    assertion bridge cost `Σ_layers (layer size)` rather than `Σ_records (layer size)`. -/
theorem azt_sub_of_filter (r : RawCircuit) (zeroConst : Nat) (azt : Nat → List RawTerm)
    (L : Nat)
    (hfilt : (r.layers.getD L ⟨0, []⟩).terms.filter (fun t => t.kIndex == zeroConst) = azt L) :
    ∀ t ∈ azt L, t ∈ (r.layers.getD L ⟨0, []⟩).terms := by
  intro t ht
  rw [← hfilt] at ht
  exact (List.mem_filter.mp ht).1

end Quadcert
