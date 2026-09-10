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

/-!
# Raw sidecar data (no Mathlib)

Field-element-free mirror of the certificate sidecar. Constants appear only as **indices**
into the circuit's constant table, so this module — and every generated data module built on
it — imports nothing.

That is deliberate and load-bearing. Measured on this toolchain, `import Mathlib` costs a
3.3 GB resident floor *per module*; a generated data module that imports it pays that floor
again, which makes parallel checking of a large circuit's chunks impossible. Raw data modules
cost ~370 MB each instead, and only the small hand-written spec module pays for Mathlib.

`quadcert/Ingest.lean` interprets these into the `Field`-valued types of `quadcert/Semantics.lean`.
-/

namespace Quadcert

/-- A quad term with its constant given by table index. -/
structure RawTerm where
  g : Nat
  h0 : Nat
  h1 : Nat
  kIndex : Nat
  deriving Repr, DecidableEq

/-- One circuit layer: `nw` is the width of the layer beneath. -/
structure RawLayer where
  nw : Nat
  terms : List RawTerm
  deriving Repr

/-- A DAG node. `sum` terms are `(kIndex, w0, w1)`. -/
inductive RawNode where
  | input (pos : Nat)
  | sum (terms : List (Nat × Nat × Nat))
  | assert0 (w : Nat)
  deriving Repr

/-- An assertion record: the node pinned to zero and the wire carrying the constraint. -/
structure RawAssert where
  assertedNode : Nat
  wireLayer : Nat
  wireIndex : Nat
  deriving Repr, DecidableEq

/-- Everything the Lean checker ingests, verbatim from `cert.rs`. -/
structure RawCircuit where
  ninput : Nat
  npublicInput : Nat
  noutput : Nat
  /-- `ceil_log2 noutput`; carried so the Lean object determines everything `compute_id`
      hashes, rather than only what the current proofs happen to read. -/
  logv : Nat
  /-- Index splitting subfield from extension-field inputs (`RawCircuit::subfield_boundary`).
      Unused by the single-field proofs, load-bearing for mdoc's two-field setup. -/
  subfieldBoundary : Nat
  nconstants : Nat
  layers : List RawLayer
  nodes : List RawNode
  /-- Wire coordinates per node index; inputs sit at the pseudo-layer `layers.length`.

      A **function**, not a list. `List.getD` is O(n), and `okNode` performs two operand
      lookups per term, so a list makes the structural check O(nterms · nnodes) — measured at
      493 s / 12.8 GB on ECDSA2, and still timing out. The dumper emits a balanced
      if-then-else tree on the index instead; Lean's kernel has GMP-accelerated `Nat`
      comparison, so each lookup costs O(log n) with O(1) comparisons. -/
  wireFn : Nat → Option (Nat × Nat)
  asserts : List RawAssert
  /-- Input position ↔ name, from `LayoutBuilder`. Advice, reviewed once. -/
  layout : List (Nat × String)

/-! ## Accessors -/

/-- The wire of node `i`, or `none`. -/
def RawCircuit.wireOf (r : RawCircuit) (i : Nat) : Option (Nat × Nat) := r.wireFn i

/-- Node `i`, defaulting to `input 0` out of range (matching `List.getD`'s totality). -/
def RawCircuit.nodeOf (r : RawCircuit) (i : Nat) : RawNode := r.nodes.getD i (.input 0)


/-! ## The decidable structural check -/

/-- Operand `w` of a node wired at layer `L` must itself be wired at layer `L + 1`. -/
def okOperandWith (wireFn : Nat → Option (Nat × Nat)) (L w : Nat) : Bool :=
  match wireFn w with
  | some (Lw, _) => Lw == L + 1
  | none => false

/-- Operand check against a circuit. Stated directly in terms of `wireOf` so the proofs in
    `quadcert/Check.lean` see the shape they expect; `okOperand_eq` bridges to the
    parameterised form the generated chunk modules use. -/
def RawCircuit.okOperand (r : RawCircuit) (L w : Nat) : Bool :=
  match r.wireOf w with
  | some (Lw, _) => Lw == L + 1
  | none => false

/-- Node `nd` at index `i` is structurally consistent with its wire.

    Parameterised by `wireFn` and `nlayers` rather than by a `RawCircuit`, so that a generated
    *chunk* module can prove its own slice before the assembled circuit exists. Every lookup
    goes through `wireFn`, which the dumper emits as a balanced if-tree — O(log n) with
    GMP-accelerated `Nat` comparisons. -/
def okNodeWith (wireFn : Nat → Option (Nat × Nat)) (nlayers : Nat) (nd : RawNode) (i : Nat) :
    Bool :=
  match nd with
  | .input p => wireFn i == some (nlayers, p)
  | .assert0 _ => wireFn i == none
  | .sum ts =>
      match wireFn i with
      | none => false
      | some (L, _) =>
          decide (L < nlayers) &&
            ts.all (fun t =>
              decide (t.2.1 < i) && decide (t.2.2 < i) &&
                okOperandWith wireFn L t.2.1 && okOperandWith wireFn L t.2.2)

/-- Node `nd`, sitting at index `i`, is structurally consistent with its wire. -/
def RawCircuit.okNodeAt (r : RawCircuit) (nd : RawNode) (i : Nat) : Bool :=
  match nd with
  | .input p => r.wireOf i == some (r.layers.length, p)
  | .assert0 _ => r.wireOf i == none
  | .sum ts =>
      match r.wireOf i with
      | none => false
      | some (L, _) =>
          decide (L < r.layers.length) &&
            ts.all (fun t =>
              decide (t.2.1 < i) && decide (t.2.2 < i) &&
                r.okOperand L t.2.1 && r.okOperand L t.2.2)

/-- The two forms agree definitionally. This is the bridge that lets a generated chunk module
    state its slice of the check using only `wireFn` and `nlayers` — before `raw` itself
    exists — and have it count towards `RawCircuit.ok`. -/
theorem okNodeAt_eq (r : RawCircuit) (nd : RawNode) (i : Nat) :
    r.okNodeAt nd i = okNodeWith r.wireFn r.layers.length nd i := rfl

/-- Every node checks. Walks the node list **sequentially** (`zipIdx`, not `List.range` plus
    `getD`), so node access is O(1) amortized and only the wire lookups cost O(log n). -/
def RawCircuit.ok (r : RawCircuit) : Bool :=
  r.nodes.zipIdx.all (fun p => r.okNodeAt p.1 p.2)


/-- `ok` splits along any decomposition of the node list. This is what lets the dumper prove
    the structural check one chunk at a time: a whole-circuit `decide` must reduce every node
    and term in a single kernel computation, which at ECDSA2 scale exhausts memory. -/
theorem all_zipIdx_append {α : Type} (f : α × Nat → Bool) (xs ys : List α) (k : Nat) :
    ((xs ++ ys).zipIdx k).all f
      = ((xs.zipIdx k).all f && (ys.zipIdx (k + xs.length)).all f) := by
  simp only [List.zipIdx_append, List.all_append]

/-- `inv` is a left inverse of `wireFn` on the index range `[lo, lo+len)`.

    Range-parameterised for the same reason `okNodeWith` is node-parameterised: a
    whole-circuit `decide` over `okInv` is one kernel computation over every node, measured
    at 951 s / 31.2 GB on ECDSA2 — the entire cost of that build. A per-chunk `decide`
    reduces only its own range. -/
def okInvRange (wireFn : Nat → Option (Nat × Nat)) (inv : Nat × Nat → Nat)
    (lo len : Nat) : Bool :=
  (List.range' lo len).all (fun i =>
    match wireFn i with
    | some p => inv p == i
    | none => true)

/-- `okInvRange` splits, which is what lets the dumper prove it one chunk at a time. -/
theorem okInvRange_split (wireFn : Nat → Option (Nat × Nat)) (inv : Nat × Nat → Nat)
    (lo a b : Nat) :
    okInvRange wireFn inv lo (a + b)
      = (okInvRange wireFn inv lo a && okInvRange wireFn inv (lo + a) b) := by
  simp only [okInvRange, ← List.range'_append, List.all_append, Nat.one_mul]

/-- `inv` is a left inverse of the wire map on every node. -/
def RawCircuit.okInv (r : RawCircuit) (inv : Nat × Nat → Nat) : Bool :=
  (List.range r.nodes.length).all (fun i =>
    match r.wireOf i with
    | some p => inv p == i
    | none => true)

/-! ### Grouping witnesses for `sum_local`

`sum_local_of_grouping` needs two data facts per layer: that the grouped terms flatten to a
permutation of the layer's canonical term list, and that each group is homogeneous in its
output wire. Both are stated on **raw** data, where terms are `Nat`-only and so decidable;
`Ingest.toLayer_perm` / `rawTerm_hom` transport them to the interpreted layer.

The permutation witness itself, the per-node correspondence and the raw form of `Backed` live in
`quadcert/RawGroup.lean`. That is a *separate module* on purpose: `Lfc3.lean` imports this one,
so every artifact and expansion module transitively depends on it, and any edit here rebuilds
all 362 generated modules. The grouping machinery is iterated on far more often than this file
is, so it does not belong here. -/

/-- Homogeneity from a bounded check. The emitted `groupOf` is guarded to return `[]` outside
    `[0, nw)`, so a check over `List.range nw` suffices for the unbounded statement. -/
theorem hom_of_bounded (groupOf : Nat → List RawTerm) (nw : Nat)
    (hguard : ∀ i, nw ≤ i → groupOf i = [])
    (hb : (List.range nw).all (fun i => (groupOf i).all (fun t => t.g == i)) = true) :
    ∀ i, ∀ t ∈ groupOf i, t.g = i := by
  intro i t ht
  by_cases hi : i < nw
  · simp only [List.all_eq_true] at hb
    have := hb i (List.mem_range.mpr hi)
    simp only [List.all_eq_true, beq_iff_eq] at this
    exact this t ht
  · rw [hguard i (by omega)] at ht
    simp at ht

/-! ### Chunked inverse check

The whole-circuit `decide` for `okInv` costs 951 s / 31.2 GB on ECDSA2 — essentially the
entire build. The fix is to prove it one range at a time. Composition is stated over a *list
of ranges* with a contiguity side-condition rather than by splitting a numeral, because
Lean's elaborator folds `5 + (5 + (5 + 4))` back to `19` before a `a + b` rewrite can fire.
`tiles` is O(number of chunks) — 27 steps for ECDSA2, not 27,000. -/

/-- The inverse check over a list of `(lo, len)` ranges. -/
def okInvChunks (wireFn : Nat → Option (Nat × Nat)) (inv : Nat × Nat → Nat)
    (cs : List (Nat × Nat)) : Bool :=
  cs.all (fun c => okInvRange wireFn inv c.1 c.2)

/-- `cs` tiles `[lo, n)` contiguously and in order. -/
def tiles : List (Nat × Nat) → Nat → Nat → Bool
  | [], lo, n => lo == n
  | (a, len) :: rest, lo, n => (a == lo) && tiles rest (lo + len) n

theorem okInvRange_apply (wireFn : Nat → Option (Nat × Nat)) (inv : Nat × Nat → Nat)
    (lo len i : Nat) (h : okInvRange wireFn inv lo len = true)
    (h1 : lo ≤ i) (h2 : i < lo + len) :
    (match wireFn i with | some p => inv p == i | none => true) = true := by
  simp only [okInvRange, List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem tiles_mem (cs : List (Nat × Nat)) (lo n : Nat) (h : tiles cs lo n = true)
    {i : Nat} (h1 : lo ≤ i) (h2 : i < n) : ∃ c ∈ cs, c.1 ≤ i ∧ i < c.1 + c.2 := by
  induction cs generalizing lo with
  | nil =>
      simp only [tiles, beq_iff_eq] at h
      omega
  | cons c rest ih =>
      obtain ⟨a, len⟩ := c
      simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hrest⟩ := h
      by_cases hc : i < a + len
      · exact ⟨(a, len), List.mem_cons_self, h1, hc⟩
      · obtain ⟨c', hc', h1', h2'⟩ := ih (a + len) hrest (by omega)
        exact ⟨c', List.mem_cons_of_mem _ hc', h1', h2'⟩

/-- **The composition.** A contiguous tiling plus a per-range check gives the whole-circuit
    check, with no whole-circuit `decide` anywhere. -/
theorem okInv_of_chunks (r : RawCircuit) (inv : Nat × Nat → Nat) (cs : List (Nat × Nat))
    (htiles : tiles cs 0 r.nodes.length = true)
    (hchunks : okInvChunks r.wireFn inv cs = true) :
    r.okInv inv = true := by
  simp only [RawCircuit.okInv, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨c, hc, h1, h2⟩ := tiles_mem cs 0 r.nodes.length htiles (Nat.zero_le i) hi
  simp only [okInvChunks, List.all_eq_true] at hchunks
  exact okInvRange_apply r.wireFn inv c.1 c.2 i (hchunks c hc) h1 h2

/-- The whole-circuit check is the range check over `[0, nnodes)`. -/
theorem okInv_eq_range (r : RawCircuit) (inv : Nat × Nat → Nat) :
    r.okInv inv = okInvRange r.wireFn inv 0 r.nodes.length := by
  simp only [RawCircuit.okInv, okInvRange, List.range_eq_range', RawCircuit.wireOf]



end Quadcert
