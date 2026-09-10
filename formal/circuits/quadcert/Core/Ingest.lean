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

import quadcert.Core.Semantics
import quadcert.Core.RawGroup
import quadcert.Core.Raw

/-!
# Interpreting raw sidecar data

Turns the `Nat`-only `Quadcert.RawCircuit` of `quadcert/Raw.lean` into the `Field`-valued
objects `quadcert/Semantics.lean` reasons about, given a constant table `consts : Nat → F`.

Splitting here is what keeps generated data modules free of Mathlib. The spec bridge supplies
`consts` and states the *constants correspondence* — e.g. `consts 2 = -a` against the curve
parameters — as a small, separately reviewable set of equations.
-/

namespace Quadcert

variable {F : Type} [Field F]

/-- Interpretation of a raw term. -/
def rawTerm (consts : Nat → F) (t : RawTerm) : QuadTerm F :=
  ⟨t.g, t.h0, t.h1, consts t.kIndex⟩

/-- Layer terms, with constants resolved through `consts`. -/
def RawLayer.toLayer (l : RawLayer) (consts : Nat → F) : LayerData F :=
  { ninput := l.nw, terms := l.terms.map (rawTerm consts) }

/-- The layered circuit. -/
def RawCircuit.toQuad (r : RawCircuit) (consts : Nat → F) : QuadCircuitData F :=
  { ninput := r.ninput,
    noutput := r.noutput,
    layers := r.layers.map (fun l => l.toLayer consts) }

/-- The quad DAG. -/
def RawCircuit.toDag (r : RawCircuit) (consts : Nat → F) : List (DagNode F) :=
  r.nodes.map (fun n =>
    match n with
    | .input p => .input p
    | .sum ts => .sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩))
    | .assert0 w => .assert0 w)

/-- The wire map, read out of the dumped per-node wire list. -/
def RawCircuit.toWireMap (r : RawCircuit) : WireMap := r.wireFn

/-- The assertion records. -/
def RawCircuit.toRecs (r : RawCircuit) : List AssertionRec :=
  r.asserts.map (fun a =>
    { assertedNode := a.assertedNode, wireLayer := a.wireLayer, wireIndex := a.wireIndex })

/-! ### The grouping bridge

`sum_local_of_grouping` needs the layer's terms to be a permutation of a grouped flattening.
That permutation cannot be `decide`d over a symbolic field — there is no `DecidableEq F`.
It *can* be decided on the raw data, where constants are `Nat` indices, and then transported
through `toLayer`. This is the second place `Raw` being field-free earns its keep. -/

/-- A decidable permutation on raw data transports to the interpreted layer. -/
theorem toLayer_perm (l : RawLayer) (consts : Nat → F) (gs : Nat → List RawTerm) (nw : Nat)
    (h : l.terms.Perm ((List.range nw).flatMap gs)) :
    (l.toLayer consts).terms.Perm
      ((List.range nw).flatMap (fun i => (gs i).map (rawTerm consts))) := by
  have := h.map (rawTerm consts)
  simpa [RawLayer.toLayer, List.map_flatMap] using this

/-- Homogeneity likewise transports: `rawTerm` preserves `g`. -/
theorem rawTerm_hom (consts : Nat → F) (gs : Nat → List RawTerm)
    (h : ∀ i, ∀ t ∈ gs i, t.g = i) :
    ∀ i, ∀ t ∈ (gs i).map (rawTerm consts), t.g = i := by
  intro i t ht
  simp only [List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h i u hu

/-! ### The per-node correspondence, transported

`realisesRaw` is a decidable check on constant *indices*; `Realises` is a proposition about
field values. They line up because both sides read the same `consts` table, which is what makes
per-node certificates emittable into Mathlib-free modules. -/

theorem realises_of_raw (consts : Nat → F) (wireFn : Nat → Option (Nat × Nat)) (L : Nat)
    (t : RawTerm) (u : Nat × Nat × Nat) (h : realisesRaw wireFn L t u = true) :
    Realises wireFn L (rawTerm consts t) (⟨consts u.1, u.2.1, u.2.2⟩ : SumTerm F) := by
  simp only [realisesRaw, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hk, hw⟩ := h
  refine ⟨by simp only [rawTerm, hk], ?_⟩
  rcases hw with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩

theorem forall2_realises_of_raw (consts : Nat → F) (wireFn : Nat → Option (Nat × Nat)) (L : Nat) :
    ∀ (ts : List RawTerm) (us : List (Nat × Nat × Nat)), realisesAll wireFn L ts us = true →
      List.Forall₂ (Realises wireFn L) (ts.map (rawTerm consts))
        (us.map (fun u => (⟨consts u.1, u.2.1, u.2.2⟩ : SumTerm F)))
  | [], [], _ => List.Forall₂.nil
  | t :: ts, u :: us, h => by
      simp only [realisesAll, Bool.and_eq_true] at h
      exact List.Forall₂.cons (realises_of_raw consts wireFn L t u h.1)
        (forall2_realises_of_raw consts wireFn L ts us h.2)
  | [], _ :: _, h => by simp [realisesAll] at h
  | _ :: _, [], h => by simp [realisesAll] at h

private lemma getD_map' {α β : Type} (f : α → β) (l : List α) (n : Nat) (da : α) (db : β)
    (h : f da = db) : (l.map f).getD n db = f (l.getD n da) := by
  induction l generalizing n with
  | nil => simp [List.getD, h]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.getD]
      | succ k => simpa [List.getD] using ih k

lemma toQuad_layerAt (r : RawCircuit) (consts : Nat → F) (L : Nat) :
    (r.toQuad consts).layerAt L = (r.layers.getD L ⟨0, []⟩).toLayer consts :=
  getD_map' _ _ _ _ _ rfl

lemma toDag_getD' (r : RawCircuit) (consts : Nat → F) (n : Nat) :
    (r.toDag consts).getD n (.input 0) =
      (match r.nodes.getD n (.input 0) with
       | .input p => .input p
       | .sum ts => .sum (ts.map (fun t => (⟨consts t.1, t.2.1, t.2.2⟩ : SumTerm F)))
       | .assert0 w => .assert0 w) :=
  getD_map' _ _ _ (RawNode.input 0) (DagNode.input 0) rfl

/-- Recover a node's raw sum-term list from the interpreted one. -/
lemma raw_sum_of_dag_sum (r : RawCircuit) (consts : Nat → F) (n : Nat) (terms : List (SumTerm F))
    (hnode : (r.toDag consts).getD n (.input 0) = .sum terms) :
    ∃ ts, r.nodes.getD n (.input 0) = .sum ts ∧
      terms = ts.map (fun u => (⟨consts u.1, u.2.1, u.2.2⟩ : SumTerm F)) := by
  rw [toDag_getD'] at hnode
  cases hn : r.nodes.getD n (.input 0) with
  | input p => rw [hn] at hnode; simp at hnode
  | sum ts =>
      rw [hn] at hnode; simp only at hnode; injection hnode with hx; exact ⟨ts, rfl, hx.symm⟩
  | assert0 w => rw [hn] at hnode; simp at hnode

/-- Input position of a layout name, or `0` if absent. The spec bridge should pin the names it
    uses with `rfl` lemmas rather than calling this at proof time. -/
def RawCircuit.pos (r : RawCircuit) (name : String) : Nat :=
  (r.layout.find? (fun e => e.2 == name)).elim 0 (·.1)

end Quadcert
