/-
# Cone templates: one structural `decide` instead of a per-node value chain

`meaning_gen` proves each assertion's meaning with a `have`-chain over its cone, one
`interpDag_sum` step per node -- measured at ~104 ms per cone node, which puts mdoc's 303,413
assertions at roughly 30 days.

The alternative: state the cone's shape as a **template** (a topological `List TmplNode` with
holes) plus a `map` from template index to DAG node index, check the match with a single
`decide +kernel` (~4.5 ms per cone node, 20-70x cheaper), and transfer the semantics with the one
generic lemma below. The algebra a meaning lemma needs is then stated once about `tmplDag` and
instantiated per assertion by the `decide`.

Two design points earn their keep:

* The template is a **DAG**, not a tree. A 266-node cone has sharing; a tree expansion of it is
  exponential, which is why the existing sidecar `Template` is a node *list* too.
* `coneIs` compares each node's whole operand list in **one** equation. That is not merely faster
  to decide -- it hands the proof the identity `us = ts.map (fun (k,a,b) => (k, map a, map b))`
  directly, so after `interpDag_sum` fires on both sides the two folds are over the *same* list
  and match by a plain congruence, with no `Forall₂` bridge.
* The instance map is a **function**, not a list. A list makes `coneIs` O(n^2) -- five `getD`
  walks per term -- which is invisible at a 266-node cone and fatal at mdoc's largest, 94,135
  nodes: the fitted cost there is 47 hours for a single assertion. Passing a generated bisection
  makes each lookup O(log n), the same fix `nodeFn` and `wireFn` already use. A caller with a
  literal list can still pass `fun i => l.getD i 0`.
-/

import quadcert.Core.Check

namespace Quadcert

variable {F : Type} [Field F]

/-- A cone template node: a hole carrying its own index, or a sum whose operands index this
    template's own list. -/
inductive TmplNode where
  | leaf (j : Nat)
  | sum (ts : List (Nat × Nat × Nat))
  deriving Repr, DecidableEq

/-- The template as a `DagNode` list, so the existing `interpDag` theory applies unchanged.
    A hole becomes `.input j`, read out of the leaf valuation. -/
def tmplDag (consts : Nat → F) (tnodes : List TmplNode) : List (DagNode F) :=
  tnodes.map (fun tn =>
    match tn with
    | .leaf j => .input j
    | .sum ts => .sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)))

/-- Structural match of a cone against a template under `map`. The order conditions are what make
    the transfer well-founded and let `interpDag_sum` fire on both sides. -/
def coneIs (nodeFn : Nat → RawNode) (tnodes : List TmplNode) (mapFn : Nat → Nat) : Bool :=
  tnodes.zipIdx.all (fun p =>
    match p.1 with
    | .leaf j => decide (j = p.2)
    | .sum ts =>
        nodeEq (nodeFn (mapFn p.2))
            (.sum (ts.map (fun t => (t.1, mapFn t.2.1, mapFn t.2.2)))) &&
          ts.all (fun t =>
            decide (t.2.1 < p.2) && decide (t.2.2 < p.2) &&
              decide (mapFn t.2.1 < mapFn p.2) &&
                decide (mapFn t.2.2 < mapFn p.2)))

private lemma getD_map {α β : Type} (f : α → β) (l : List α) (n : Nat) (da : α) (db : β)
    (h : f da = db) : (l.map f).getD n db = f (l.getD n da) := by
  induction l generalizing n with
  | nil => simp [List.getD, h]
  | cons x xs ih =>
      cases n with
      | zero => simp [List.getD]
      | succ k => simpa [List.getD] using ih k

theorem tmplDag_length (consts : Nat → F) (tnodes : List TmplNode) :
    (tmplDag consts tnodes).length = tnodes.length := by
  simp [tmplDag]

theorem tmplDag_getD (consts : Nat → F) (tnodes : List TmplNode) (i : Nat) :
    (tmplDag consts tnodes).getD i (.input 0)
      = (match tnodes.getD i (.leaf 0) with
         | .leaf j => .input j
         | .sum ts => .sum (ts.map (fun t => ⟨consts t.1, t.2.1, t.2.2⟩))) :=
  getD_map _ _ _ _ _ rfl

/-- Pointwise-equal fold functions give equal folds. -/
theorem foldl_congr {α : Type} (l : List α) (f g : F → α → F)
    (h : ∀ acc a, a ∈ l → f acc a = g acc a) (init : F) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.foldl_cons]
      rw [h init a (List.mem_cons_self ..)]
      exact ih (fun acc b hb => h acc b (List.mem_cons_of_mem _ hb)) _

/-- The match, read off at one template index. -/
theorem coneIs_at (nodeFn : Nat → RawNode) (tnodes : List TmplNode) (mapFn : Nat → Nat)
    (h : coneIs nodeFn tnodes mapFn = true) {i : Nat} (hi : i < tnodes.length) :
    (match tnodes.getD i (.leaf 0) with
     | .leaf j => j = i
     | .sum ts =>
         nodeFn (mapFn i)
             = .sum (ts.map (fun t => (t.1, mapFn t.2.1, mapFn t.2.2))) ∧
           ∀ t ∈ ts, t.2.1 < i ∧ t.2.2 < i ∧
             mapFn t.2.1 < mapFn i ∧ mapFn t.2.2 < mapFn i) := by
  simp only [coneIs, List.all_eq_true] at h
  have hmem := h (tnodes.getD i (.leaf 0), i) (by
    simp only [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some])
  cases hnd : tnodes.getD i (.leaf 0) with
  | leaf j =>
      rw [hnd] at hmem
      simpa using hmem
  | sum ts =>
      rw [hnd] at hmem
      simp only [Bool.and_eq_true, List.all_eq_true] at hmem
      refine ⟨eq_of_nodeEq hmem.1, fun t ht => ?_⟩
      have hb := hmem.2 t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩

/-- **The semantic transfer.** A structural match plus the raw-node agreement is enough: every
    template index evaluates, in the template's own dag under the leaf valuation, to exactly what
    the matched cone node evaluates to in the real dag. -/
theorem coneIs_transfer (r : RawCircuit) (consts inputs : Nat → F) (nodeFn : Nat → RawNode)
    (hfn : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    (tnodes : List TmplNode) (mapFn : Nat → Nat)
    (hcone : coneIs nodeFn tnodes mapFn = true)
    (hmap : ∀ i, i < tnodes.length → mapFn i < r.nodes.length) :
    ∀ i, i < tnodes.length →
      interpDag (r.toDag consts) inputs (mapFn i)
        = interpDag (tmplDag consts tnodes)
            (fun h => interpDag (r.toDag consts) inputs (mapFn h)) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hat := coneIs_at nodeFn tnodes mapFn hcone hi
    cases hnd : tnodes.getD i (.leaf 0) with
    | leaf j =>
        rw [hnd] at hat
        rw [interpDag_input (tmplDag consts tnodes)
          (fun h => interpDag (r.toDag consts) inputs (mapFn h)) i j
          (by rw [tmplDag_length]; exact hi)
          (by rw [tmplDag_getD, hnd]), hat]
    | sum ts =>
        rw [hnd] at hat
        obtain ⟨hus, hord⟩ := hat
        have hdagget : (r.toDag consts).getD (mapFn i) (.input 0)
            = .sum ((ts.map (fun t => (t.1, mapFn t.2.1, mapFn t.2.2))).map
                      (fun t => ⟨consts t.1, t.2.1, t.2.2⟩)) := by
          rw [toDag_getD_fn r consts nodeFn hfn (hmap i hi), hus]; rfl
        rw [interpDag_sum inputs _ _ _ hdagget (by
          intro t ht
          simp only [List.mem_map] at ht
          obtain ⟨u, ⟨v, hv, rfl⟩, rfl⟩ := ht
          exact ⟨(hord v hv).2.2.1, (hord v hv).2.2.2⟩)]
        rw [interpDag_sum _ (tmplDag consts tnodes) i _
          (by rw [tmplDag_getD, hnd]) (by
          intro t ht
          simp only [List.mem_map] at ht
          obtain ⟨v, hv, rfl⟩ := ht
          exact ⟨(hord v hv).1, (hord v hv).2.1⟩)]
        simp only [List.foldl_map]
        refine foldl_congr ts _ _ (fun acc t ht => ?_) 0
        have h0 := ih t.2.1 (hord t ht).1 (Nat.lt_trans (hord t ht).1 hi)
        have h1 := ih t.2.2 (hord t ht).2.1 (Nat.lt_trans (hord t ht).2.1 hi)
        rw [h0, h1]

end Quadcert
