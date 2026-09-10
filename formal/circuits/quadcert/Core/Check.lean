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

import quadcert.Core.Ingest

/-!
# Structural checks on raw sidecar data

`ValidScheduling` has eight fields. Seven of them are *structural* — they say the wire map
agrees with the DAG's shape — and this file discharges all seven **generically**, from a
decidable predicate on `RawCircuit`.

That genericity is the point. Rung 0 and Rung 1 proved these fields by a `match` over every
node index, which is fine at 9 or 19 nodes and impossible at the 26,939 of ECDSA2: one
`match` with 26,939 branches is a single term that cannot be split across modules. Proving
the fields once, about arbitrary raw data, replaces that enumeration with a computation the
generated module performs on its own data.

The eighth field, `sum_local`, is *not* structural — it is an equation between field
expressions — and is still supplied by the caller. See `CIRCUIT_PROOF_PLAN.md`.
-/

namespace Quadcert

variable {F : Type} [Field F]

/-! ## List helper -/

private lemma getD_map {α β : Type} (f : α → β) (l : List α) (n : Nat) (da : α) (db : β)
    (h : f da = db) : (l.map f).getD n db = f (l.getD n da) := by
  induction l generalizing n with
  | nil => simp [List.getD, h]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.getD]
      | succ k => simpa [List.getD] using ih k

/-- Interpretation of a single raw node. -/
def rawNode (consts : Nat → F) : RawNode → DagNode F
  | .input p => .input p
  | .sum ts => .sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩))
  | .assert0 w => .assert0 w

lemma toDag_getD (r : RawCircuit) (consts : Nat → F) (n : Nat) :
    (r.toDag consts).getD n (.input 0) = rawNode consts (r.nodeOf n) :=
  getD_map _ _ _ _ _ rfl

lemma toWireMap_eq (r : RawCircuit) (n : Nat) : r.toWireMap n = r.wireOf n := rfl

lemma toQuad_layers_length (r : RawCircuit) (consts : Nat → F) :
    (r.toQuad consts).layers.length = r.layers.length := by
  simp [RawCircuit.toQuad]

lemma ok_node (r : RawCircuit) (h : r.ok = true) {i : Nat} (hi : i < r.nodes.length) :
    r.okNodeAt (r.nodeOf i) i = true := by
  simp only [RawCircuit.ok, List.all_eq_true] at h
  refine h (r.nodeOf i, i) ?_
  simp only [List.mem_zipIdx_iff_getElem?, RawCircuit.nodeOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-! ## Injectivity via an emitted inverse

Checking injectivity of a 26,939-entry map by case analysis is quadratic. The dumper emits a
left inverse instead, and the check becomes linear: one lookup per node. -/

lemma okInv_apply (r : RawCircuit) {inv : Nat × Nat → Nat} (h : r.okInv inv = true)
    {i : Nat} (hi : i < r.nodes.length) {p : Nat × Nat} (hp : r.wireOf i = some p) :
    inv p = i := by
  simp only [RawCircuit.okInv, List.all_eq_true] at h
  have := h i (by simp [hi])
  rw [hp] at this
  simpa using this

/-! ## The generic structural theorem -/

/-- **Seven of the eight `ValidScheduling` fields, discharged generically.**

`sum_local` is the exception: it is an equation between field expressions, not a structural
fact, so the caller supplies it. Everything else follows from two decidable checks on the raw
data — `ok` and `okInv` — which the generated module discharges by computation on its own
data rather than by enumerating nodes. -/
theorem validScheduling_of_checks (r : RawCircuit) (consts : Nat → F) (inputs : Nat → F)
    (inv : Nat × Nat → Nat) (hok : r.ok = true) (hinv : r.okInv inv = true)
    (hlt : ∀ i p, r.wireFn i = some p → i < r.nodes.length)
    (hlocal : ∀ n L g terms,
      (r.toDag consts).getD n (.input 0) = .sum terms → r.toWireMap n = some (L, g) →
      evalLayer ((r.toQuad consts).layerAt L) ((r.toQuad consts).inputValuation inputs L) g =
        nodeSum (r.toDag consts) r.toWireMap
          ((r.toQuad consts).inputValuation inputs L) (L + 1) n) :
    ValidScheduling (r.toQuad consts) (r.toDag consts) r.toWireMap inputs := by
  -- every wired node is in range; the dumper guards `wireFn` so this is one line per circuit
  have hrange : ∀ n p, r.wireOf n = some p → n < r.nodes.length := hlt
  have hdaglen : (r.toDag consts).length = r.nodes.length := by simp [RawCircuit.toDag]
  refine
    { map_inrange := ?_, wire_inj := ?_, input_wire := ?_, assert0_nowire := ?_,
      sum_inrange := ?_, sum_operands := ?_, sum_operands_lt := ?_, sum_local := hlocal }
  · intro n L g h
    rw [hdaglen]
    exact hrange n (L, g) h
  · intro m n L g hm hn
    rw [← okInv_apply r hinv (hrange m _ hm) hm, ← okInv_apply r hinv (hrange n _ hn) hn]
  · intro n pos hn h
    rw [toDag_getD] at h
    have hin : r.nodeOf n = .input pos := by
      cases hnode : r.nodeOf n with
      | input p => rw [hnode] at h; simp only [rawNode] at h; injection h with hp; subst hp; rfl
      | sum ts => rw [hnode] at h; simp [rawNode] at h
      | assert0 w => rw [hnode] at h; simp [rawNode] at h
    have hchk := ok_node r hok (by omega : n < r.nodes.length)
    rw [RawCircuit.okNodeAt.eq_def, hin] at hchk
    rw [toWireMap_eq, toQuad_layers_length]
    simpa using hchk
  · intro n w h
    rw [toDag_getD] at h
    have ha : r.nodeOf n = .assert0 w := by
      cases hnode : r.nodeOf n with
      | input p => rw [hnode] at h; simp [rawNode] at h
      | sum ts => rw [hnode] at h; simp [rawNode] at h
      | assert0 x => rw [hnode] at h; simp only [rawNode] at h; injection h with hx; subst hx; rfl
    by_cases hn : n < r.nodes.length
    · have hchk := ok_node r hok hn
      rw [RawCircuit.okNodeAt.eq_def, ha] at hchk
      rw [toWireMap_eq]; simpa using hchk
    · rw [toWireMap_eq]
      by_contra hc
      cases hw : r.wireOf n with
      | none => exact hc hw
      | some p => exact absurd (hlt n p hw) (by omega)
  · intro n L g terms h hmap
    have hn := hrange n (L, g) (by rw [← toWireMap_eq]; exact hmap)
    rw [toDag_getD] at h
    have hs : ∃ ts, r.nodeOf n = .sum ts := by
      cases hnode : r.nodeOf n with
      | input p => rw [hnode] at h; simp [rawNode] at h
      | sum ts => exact ⟨ts, rfl⟩
      | assert0 x => rw [hnode] at h; simp [rawNode] at h
    obtain ⟨ts, hts⟩ := hs
    have hchk := ok_node r hok hn
    rw [toWireMap_eq] at hmap
    simp only [RawCircuit.okNodeAt.eq_def, hts, hmap, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hchk
    rw [toQuad_layers_length]
    exact hchk.1
  · intro n L g terms t h hmap ht
    have hn := hrange n (L, g) (by rw [← toWireMap_eq]; exact hmap)
    rw [toDag_getD] at h
    have hs : ∃ ts, r.nodeOf n = .sum ts ∧
        terms = ts.map (fun u => (⟨consts u.1, u.2.1, u.2.2⟩ : SumTerm F)) := by
      cases hnode : r.nodeOf n with
      | input p => rw [hnode] at h; simp [rawNode] at h
      | sum ts => rw [hnode] at h; simp only [rawNode] at h; injection h with hx; exact ⟨ts, rfl, hx.symm⟩
      | assert0 x => rw [hnode] at h; simp [rawNode] at h
    obtain ⟨ts, hts, hterms⟩ := hs
    have hchk := ok_node r hok hn
    rw [toWireMap_eq] at hmap ⊢
    simp only [RawCircuit.okNodeAt.eq_def, hts, hmap, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hchk
    subst hterms
    simp only [List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    obtain ⟨_, hall⟩ := hchk
    have hu' := hall u hu
    obtain ⟨⟨⟨_, _⟩, ho0⟩, ho1⟩ := hu'
    constructor
    · cases hw : r.wireOf u.2.1 with
      | none =>
          unfold RawCircuit.okOperand at ho0; rw [hw] at ho0; simp at ho0
      | some q =>
          obtain ⟨Lq, iq⟩ := q
          unfold RawCircuit.okOperand at ho0
          rw [hw] at ho0
          simp only [beq_iff_eq] at ho0
          subst ho0
          exact ⟨iq, by first | rfl | exact hw⟩
    · cases hw : r.wireOf u.2.2 with
      | none =>
          unfold RawCircuit.okOperand at ho1; rw [hw] at ho1; simp at ho1
      | some q =>
          obtain ⟨Lq, iq⟩ := q
          unfold RawCircuit.okOperand at ho1
          rw [hw] at ho1
          simp only [beq_iff_eq] at ho1
          subst ho1
          exact ⟨iq, by first | rfl | exact hw⟩
  · intro n terms h t ht
    rw [toDag_getD] at h
    by_cases hn : n < r.nodes.length
    · have hs : ∃ ts, r.nodeOf n = .sum ts ∧
          terms = ts.map (fun u => (⟨consts u.1, u.2.1, u.2.2⟩ : SumTerm F)) := by
        cases hnode : r.nodeOf n with
        | input p => rw [hnode] at h; simp [rawNode] at h
        | sum ts => rw [hnode] at h; simp only [rawNode] at h; injection h with hx; exact ⟨ts, rfl, hx.symm⟩
        | assert0 x => rw [hnode] at h; simp [rawNode] at h
      obtain ⟨ts, hts, hterms⟩ := hs
      have hchk := ok_node r hok hn
      cases hw : r.wireOf n with
      | none =>
          simp only [RawCircuit.okNodeAt.eq_def, hts, hw] at hchk
          exact absurd hchk (by simp)
      | some q =>
          obtain ⟨L, g⟩ := q
          simp only [RawCircuit.okNodeAt.eq_def, hts, hw, Bool.and_eq_true, List.all_eq_true,
            decide_eq_true_eq] at hchk
          subst hterms
          simp only [List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          have hu' := hchk.2 u hu
          exact ⟨hu'.1.1.1, hu'.1.1.2⟩
    · have : r.nodeOf n = .input 0 :=
        List.getD_eq_default _ _ (by omega)
      rw [this] at h; simp [rawNode] at h

/-- A node's interpreted form, read through the emitted bisection rather than by walking the
    node list. This is what makes a per-assertion meaning lemma affordable: the cone of one
    ECDSA2 assertion is 118 nodes, and each needs its own `getD`. -/
theorem toDag_getD_fn (r : RawCircuit) (consts : Nat → F) (nodeFn : Nat → RawNode)
    (h : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    {n : Nat} (hn : n < r.nodes.length) :
    (r.toDag consts).getD n (.input 0) = rawNode consts (nodeFn n) := by
  rw [toDag_getD, nodeFn_apply r nodeFn h hn]

/-! ## `sum_local`, from decidable raw data

The eighth field. Everything it consumes is a check on raw data:

* `hperm` — one `msort` equality per layer, O(n log n) and kernel-reducible (see `Raw.msort`);
* `hhom` — one bounded `decide` per layer;
* `hcorr` — the per-node correspondence, chunkable exactly like `ok_k`.

The `g` bound and `L < nlayers` both come from checks that already exist: `groupOkWith` carries
`g < gbound L`, and `ok` carries `L < nlayers` for every sum node. So no extra generated check.

The cost of *instantiating* this at a node is the node's own arity, not the layer's:
`evalLayer_eq_foldGroup` is generic in the layer, so its O(nwires) walk happens once inside the
proof rather than once per node. That difference is 4,066× in term-mentions on ECDSA2. -/
theorem sum_local_of_raw (r : RawCircuit) (consts inputs : Nat → F)
    (groupOf : Nat → Nat → List RawTerm) (gbound : Nat → Nat)
    (hok : r.ok = true)
    (hlt : ∀ i p, r.wireFn i = some p → i < r.nodes.length)
    (hperm : ∀ L, L < r.layers.length → (r.layers.getD L ⟨0, []⟩).terms.Perm
      ((List.range (gbound L)).flatMap (groupOf L)))
    (hhom : ∀ L, L < r.layers.length → ∀ i, ∀ t ∈ groupOf L i, t.g = i)
    (hcorr : r.nodes.zipIdx.all
      (fun p => groupOkWith r.wireFn gbound groupOf p.1 p.2) = true) :
    ∀ n L g terms,
      (r.toDag consts).getD n (.input 0) = .sum terms → r.toWireMap n = some (L, g) →
      evalLayer ((r.toQuad consts).layerAt L) ((r.toQuad consts).inputValuation inputs L) g =
        nodeSum (r.toDag consts) r.toWireMap
          ((r.toQuad consts).inputValuation inputs L) (L + 1) n := by
  intro n L g terms hnode hmap
  obtain ⟨ts, hts, rfl⟩ := raw_sum_of_dag_sum r consts n terms hnode
  have hn : n < r.nodes.length := hlt n (L, g) hmap
  -- `ok` already pins the layer in range for every sum node
  have hts' : r.nodeOf n = .sum ts := hts
  have hL : L < r.layers.length := by
    have hchk := ok_node r hok hn
    rw [RawCircuit.okNodeAt.eq_def, hts', show r.wireOf n = some (L, g) from hmap] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    exact hchk.1
  -- this node's slice of the correspondence check
  have hchunk : groupOkWith r.wireFn gbound groupOf (r.nodes.getD n (.input 0)) n = true := by
    simp only [List.all_eq_true] at hcorr
    refine hcorr (r.nodes.getD n (.input 0), n) ?_
    simp only [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn, Option.getD_some]
  rw [hts] at hchunk
  simp only [groupOkWith, show r.wireFn n = some (L, g) from hmap, Bool.and_eq_true,
    decide_eq_true_eq] at hchunk
  refine sum_local_of_grouping (r.toQuad consts) (r.toDag consts) r.toWireMap inputs L g n
    (gbound L) (fun i => (groupOf L i).map (rawTerm consts)) _ ?_ ?_ hchunk.1 hnode ?_
  · rw [toQuad_layerAt]
    exact toLayer_perm _ consts (groupOf L) (gbound L) (hperm L hL)
  · exact rawTerm_hom consts (groupOf L) (hhom L hL)
  · exact forall2_realises_of_raw consts r.wireFn L (groupOf L g) ts hchunk.2

/-- **All eight fields.** `ValidScheduling` with no residual hypothesis: every input is a
    decidable check on the raw data, and the generated modules discharge each one on their own
    slice. -/
theorem validScheduling_of_raw (r : RawCircuit) (consts inputs : Nat → F)
    (inv : Nat × Nat → Nat) (groupOf : Nat → Nat → List RawTerm) (gbound : Nat → Nat)
    (hok : r.ok = true) (hinv : r.okInv inv = true)
    (hlt : ∀ i p, r.wireFn i = some p → i < r.nodes.length)
    (hperm : ∀ L, L < r.layers.length → (r.layers.getD L ⟨0, []⟩).terms.Perm
      ((List.range (gbound L)).flatMap (groupOf L)))
    (hhom : ∀ L, L < r.layers.length → ∀ i, ∀ t ∈ groupOf L i, t.g = i)
    (hcorr : r.nodes.zipIdx.all
      (fun p => groupOkWith r.wireFn gbound groupOf p.1 p.2) = true) :
    ValidScheduling (r.toQuad consts) (r.toDag consts) r.toWireMap inputs :=
  validScheduling_of_checks r consts inputs inv hok hinv hlt
    (sum_local_of_raw r consts inputs groupOf gbound hok hlt hperm hhom hcorr)

/-! ## `Backed`, from decidable raw data

The soundness direction only. `assertions_zero_of_accepts` consumes exactly this. -/

theorem backed_of_rawWith (r : RawCircuit) (consts : Nat → F) (zeroConst : Nat)
    (hz : consts zeroConst = 0) (azt : Nat → List RawTerm)
    (hsub : ∀ L, ∀ t ∈ azt L, t ∈ (r.layers.getD L ⟨0, []⟩).terms)
    (a : RawAssert) (h : backedRawWith r zeroConst azt a = true) :
    Backed (r.toQuad consts) r.toWireMap
      ⟨a.assertedNode, a.wireLayer, a.wireIndex⟩ := by
  simp only [backedRawWith, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hl, hmid⟩ | ⟨hi, hmap⟩
  · -- materialized mid-circuit assertion term
    left
    refine ⟨by rwa [toQuad_layers_length], ?_⟩
    cases hw : r.wireFn a.assertedNode with
    | none => rw [hw] at hmid; simp at hmid
    | some p =>
        rw [hw] at hmid
        simp only [Bool.and_eq_true, beq_iff_eq] at hmid
        obtain ⟨hL, hany⟩ := hmid
        -- the witness is in `azt`, hence in the layer
        have hmem : (⟨a.wireIndex, p.2, p.2, zeroConst⟩ : RawTerm) ∈
            (r.layers.getD a.wireLayer ⟨0, []⟩).terms := by
          obtain ⟨t, ht, hteq⟩ := List.any_eq_true.mp hany
          rw [beq_iff_eq] at hteq
          exact hteq ▸ hsub a.wireLayer t ht
        refine ⟨p.2, ?_, ?_⟩
        · show r.wireFn a.assertedNode = _
          rw [hw, ← hL]
        · rw [toQuad_layerAt]
          have := List.mem_map_of_mem (f := rawTerm consts) hmem
          simpa [RawLayer.toLayer, rawTerm, hz] using this
  · -- last-layer output wire
    right
    refine ⟨by simpa [RawCircuit.toQuad] using hi, ?_⟩
    show r.wireFn a.assertedNode = _
    simpa using hmap

/-- Every record is backed, from one decidable check on the assertion list. -/
theorem all_backed_of_rawWith (r : RawCircuit) (consts : Nat → F) (zeroConst : Nat)
    (hz : consts zeroConst = 0) (azt : Nat → List RawTerm)
    (hsub : ∀ L, ∀ t ∈ azt L, t ∈ (r.layers.getD L ⟨0, []⟩).terms)
    (h : r.asserts.all (backedRawWith r zeroConst azt) = true) :
    ∀ a ∈ r.toRecs, Backed (r.toQuad consts) r.toWireMap a := by
  intro a ha
  simp only [RawCircuit.toRecs, List.mem_map] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  simp only [List.all_eq_true] at h
  exact backed_of_rawWith r consts zeroConst hz azt hsub u (h u hu)

/-! ### Constants correspondence

The dumper emits the constant table as canonical integers from the artifact's own encoding.
The negated constants — `-1`, `-a`, `-b` — appear as `p - n`, so relating them to
`CurveParameters` needs the field's characteristic. This is the one place the P-256 choice
enters the proof, and it enters as a hypothesis rather than as a comment. -/

/-- In characteristic `p`, the canonical encoding `p - n` of a negated constant casts to
    `-n`. No numeral computation on the 256-bit value is needed — only `n < p`. -/
theorem cast_sub_eq_neg {F : Type} [Field F] (p n : Nat) [CharP F p] (h : n ≤ p) :
    ((p - n : Nat) : F) = -(n : F) := by
  have : ((p - n : Nat) : F) = (p : F) - (n : F) := by
    rw [Nat.cast_sub h]
  rw [this, CharP.cast_eq_zero, zero_sub]

end Quadcert
