/-
# Edge lists as the unit of verification

An assertion's meaning has two halves: *what it says* (a template lemma, proved once per class)
and *that the circuit actually says it* (a structural match, per instance). Treating the second as
per-instance bookkeeping is what made it expensive. Treating the **edge list** as the object --
"these N instances all realise this one template" -- makes it one `decide`.

`coneIs` already takes the instance map as a function, so an edge list is just a
`mapOf : Nat → Nat → Nat`: edge index, then template index. The generator emits it as a bisection,
the way it already emits `nodeFn` and `wireFn`. Nothing here is specific to a particular
obligation -- `edges_transfer` hands every edge the same `interpDag` equality that
`coneIs_transfer` gives one cone, so any template lemma applies across a whole class at once.

The skew that makes this pay: mdoc_hash puts **284,703 of its 303,413 assertions** in a single
3-node `is_boolean` class. One edge list, one template, one `decide`.
-/

import quadcert.Core.ConeTmpl

namespace Quadcert

variable {F : Type} [Field F]

/-- `n` instances of one template, matched in a single decidable check. -/
def edgesMatch (nodeFn : Nat → RawNode) (tnodes : List TmplNode)
    (mapOf : Nat → Nat → Nat) (n : Nat) : Bool :=
  (List.range n).all (fun e => coneIs nodeFn tnodes (mapOf e))

/-- One contiguous slice of an edge list. A single `decide` over all 6,656 SHA-256 booleanity
    edges needs close to the 16 GB cap and is not reliably reproducible; slices of 512 cost
    ~7 s each and sit far below it. Same chunking discipline as every other family here. -/
def edgesMatchAt (nodeFn : Nat → RawNode) (tnodes : List TmplNode)
    (mapOf : Nat → Nat → Nat) (lo n : Nat) : Bool :=
  (List.range' lo n).all (fun e => coneIs nodeFn tnodes (mapOf e))

/-- Slices that tile `[0, n)` compose, mirroring `Raw.okInv_of_chunks`. The tiling is checked as
    data rather than by splitting a numeral, for the reason `Raw.lean:226` records. -/
theorem edgesMatch_of_chunks (nodeFn : Nat → RawNode) (tnodes : List TmplNode)
    (mapOf : Nat → Nat → Nat) (cs : List (Nat × Nat)) (n : Nat)
    (htiles : tiles cs 0 n = true)
    (hall : ∀ c ∈ cs, edgesMatchAt nodeFn tnodes mapOf c.1 c.2 = true) :
    edgesMatch nodeFn tnodes mapOf n = true := by
  simp only [edgesMatch, List.all_eq_true, List.mem_range]
  intro e he
  obtain ⟨c, hc, h1, h2⟩ := tiles_mem cs 0 n htiles (Nat.zero_le e) he
  have := hall c hc
  simp only [edgesMatchAt, List.all_eq_true] at this
  exact this e (List.mem_range'_1.mpr ⟨h1, h2⟩)

/-- **Transfer across a whole edge list.** Every edge gets the same conclusion `coneIs_transfer`
    gives a single cone, so a template lemma proved once covers the entire class. -/
theorem edges_transfer (r : RawCircuit) (consts inputs : Nat → F) (nodeFn : Nat → RawNode)
    (hfn : (r.nodes.zipIdx.all fun p => nodeEq (nodeFn p.2) p.1) = true)
    (tnodes : List TmplNode) (mapOf : Nat → Nat → Nat) (n : Nat)
    (hedges : edgesMatch nodeFn tnodes mapOf n = true)
    (hmap : ∀ e, e < n → ∀ i, i < tnodes.length → mapOf e i < r.nodes.length) :
    ∀ e, e < n → ∀ i, i < tnodes.length →
      interpDag (r.toDag consts) inputs (mapOf e i)
        = interpDag (tmplDag consts tnodes)
            (fun h => interpDag (r.toDag consts) inputs (mapOf e h)) i := by
  intro e he i hi
  have hc : coneIs nodeFn tnodes (mapOf e) = true := by
    simp only [edgesMatch, List.all_eq_true, List.mem_range] at hedges
    exact hedges e he
  exact coneIs_transfer r consts inputs nodeFn hfn tnodes (mapOf e) hc (hmap e he) i hi

end Quadcert
