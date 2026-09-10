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

module

public import Mathlib

/-!
# Quad-circuit semantics (Phase 1 of `CIRCUIT_PROOF_PLAN.md`)

Field-generic semantics of the certificate sidecar produced by
`compile_compiler::cert` (`rust/compile/compiler/src/cert.rs`), and a proof that the
runtime's **layer-by-layer evaluation** agrees with the **DAG interpretation** the spec
bridge reasons about.

Two equivalent views of one computation:

* `evalLayer` / `layerValuations` / `wireValue` — the layer semantics, faithful to the Rust
  reference evaluator `compile/eval/src/eval.rs`. A term `(g, h0, h1, k)` with `k ≠ 0`
  accumulates `k · v[h0] · v[h1]` into output wire `g`; a term with `k = 0` is an
  *assertion* that `v[h0] · v[h1] = 0`.

* `interpDag` — the DAG interpretation, the self-interpreting semantic object: a `sum` node
  computes `Σᵢ kᵢ · interp(w0ᵢ) · interp(w1ᵢ)` from its operands, and input position `0` is
  the constant one, so copy chains evaluate to the copied value.

The **simulation theorem** (`simulation`) proves that, under a valid scheduling
(`ValidScheduling`) of the DAG into layers, the layer value of every wire equals the DAG
interpretation of the node mapped to it. This single lemma absorbs all compiler
optimizations (algsimp / CSE / copy insertion / scheduling): the dumped DAG is
self-interpreting and only the endpoint correspondence is checked.

## Assertion mechanisms

`Accepts` captures both mechanisms used by the compiler:

* mid-circuit asserts are materialized as a term `(g, w, w, 0)`; the assertion holds iff
  `v[w] · v[w] = 0`, which over a field is equivalent to `v[w] = 0` (`sq_eq_zero`);
* last-layer asserts are circuit outputs required to be zero.

List indexing uses `List.getD` (total, default-returning); there is no `List.get?` in this
toolchain.
-/

@[expose] public section

open BigOperators

variable {F : Type} [Field F]

/-! ## List helpers (this toolchain has `getD`/`get`, not `get?`) -/

private lemma getD_take_of_lt {α : Type} (xs : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    xs.getD i d = (xs.take (i + 1)).getD i d := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs' ih =>
      cases i with
      | zero => simp [List.getD, List.take]
      | succ i =>
          have hlen : i < xs'.length :=
            Nat.lt_of_succ_lt_succ (by simpa [List.length] using hi)
          simpa [List.getD, List.take] using ih i hlen

private lemma getD_append_last {α : Type} (acc : List α) (v : α) (d : α) :
    (acc ++ [v]).getD acc.length d = v := by
  induction acc with
  | nil => rfl
  | cons x acc' ih =>
      change (acc' ++ [v]).getD acc'.length d = v
      exact ih

/-- Two folds over the same list agree when their step functions agree on the list's own
    elements. Used to replace the operand valuations inside a quad term list without
    reasoning about the accumulator. -/
private lemma foldl_congr_mem {α β : Type} (f g : β → α → β) (l : List α)
    (h : ∀ b, ∀ a ∈ l, f b a = g b a) (z : β) : l.foldl f z = l.foldl g z := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [h z a (by simp)]
      exact ih (fun b a' ha' => h b a' (by simp [ha'])) _

/-! ## Layer data -/

/-- A single quad term. Contributes `k · v[h0] · v[h1]` to output wire `g`.
    When `k = 0`, it is instead an assertion that `v[h0] · v[h1] = 0`. -/
structure QuadTerm (F : Type) where
  g : Nat
  h0 : Nat
  h1 : Nat
  k : F

/-- One circuit layer. `ninput` is the number of wires in the layer beneath it;
    `terms` are the layer's quad terms in canonical order. -/
structure LayerData (F : Type) where
  ninput : Nat
  terms : List (QuadTerm F)

/-- Expanded quad circuit in protocol layer order: `layers.get? 0` is the output layer and
    the deepest layer is last. Mirrors `core_proto::circuit::RawCircuit`. -/
structure QuadCircuitData (F : Type) where
  ninput : Nat
  noutput : Nat
  layers : List (LayerData F)

namespace QuadCircuitData

abbrev nlayers (c : QuadCircuitData F) : Nat := c.layers.length

/-- The layer at index `l`, or an empty default when out of range. In-range callers use
    `layerAt_mem`. -/
def layerAt (c : QuadCircuitData F) (l : Nat) : LayerData F :=
  c.layers.getD l { ninput := 0, terms := [] }

lemma layerAt_mem (c : QuadCircuitData F) (l : Nat) (h : l < c.layers.length) :
    c.layerAt l = c.layers.get ⟨l, h⟩ := by
  dsimp [layerAt]
  exact List.getD_eq_get c.layers _ ⟨l, h⟩

end QuadCircuitData

/-! ## Layer semantics (faithful to `eval.rs`) -/

/-- Evaluate one layer on the valuation `vin` of the layer beneath. The value of output wire
    `g` is the sum of `k · vin[h0] · vin[h1]` over the layer's terms with that `g`. Terms
    with `k = 0` contribute `0` here; they are handled as assertions by `layerFails`. -/
def evalLayer (layer : LayerData F) (vin : Nat → F) : Nat → F :=
  fun g => layer.terms.foldl
    (fun acc t => if t.g = g then acc + t.k * vin t.h0 * vin t.h1 else acc) 0

/-- A layer *fails* on `vin` if some assertion term `(g, h0, h1, 0)` has a non-zero product
    `vin[h0] · vin[h1]`. -/
def layerFails (layer : LayerData F) (vin : Nat → F) : Prop :=
  ∃ t ∈ layer.terms, t.k = 0 ∧ vin t.h0 * vin t.h1 ≠ 0

/-- Valuations of every layer in `layers`, indexed by protocol layer order, computed
    deepest-first. The second argument is the valuation feeding the deepest layer (the
    circuit inputs). The result lists each layer's valuation in the same order as `layers`
    (`0` = output layer). -/
def valuationsAux : List (LayerData F) → (Nat → F) → List (Nat → F)
  | [], _ => []
  | [layer], below => [evalLayer layer below]
  | layer :: rest@(_ :: _), below =>
      let restVals := valuationsAux rest below
      evalLayer layer (restVals.getD 0 (fun _ => 0)) :: restVals

/-- Valuations of every layer of `c`, indexed by protocol layer (`0` = output layer). -/
def layerValuations (c : QuadCircuitData F) (inputs : Nat → F) : List (Nat → F) :=
  valuationsAux c.layers inputs

theorem valuationsAux_length (layers : List (LayerData F)) (below : Nat → F) :
    (valuationsAux layers below).length = layers.length := by
  induction layers with
  | nil => simp [valuationsAux]
  | cons layer rest ih =>
      cases rest with
      | nil => simp [valuationsAux]
      | cons r rest' => simp [valuationsAux, ih]

/-- Value of the wire at `(layer, index)`. Real layers are read from `layerValuations`; the
    pseudo-layer `nlayers` is the circuit input. -/
def wireValue (c : QuadCircuitData F) (inputs : Nat → F) (layer index : Nat) : F :=
  if h : layer < c.layers.length then
    (layerValuations c inputs).getD layer (fun _ => 0) index
  else if layer = c.layers.length then
    inputs index
  else
    0

/-- The input valuation feeding layer `l`: the valuation of layer `l + 1`, or the circuit
    inputs when `l` is the deepest layer. Defined via `wireValue` so the connection to the
    layer beneath is definitional. -/
def QuadCircuitData.inputValuation (c : QuadCircuitData F) (inputs : Nat → F) (l : Nat) :
    Nat → F :=
  fun i => if l + 1 < c.layers.length then wireValue c inputs (l + 1) i else inputs i

/-- The circuit fails on `inputs` if some layer has a failing assertion term, evaluated on
    that layer's input valuation. -/
def circuitFails (c : QuadCircuitData F) (inputs : Nat → F) : Prop :=
  ∃ l < c.layers.length, layerFails (c.layerAt l) (c.inputValuation inputs l)

/-- All output wires are zero. -/
def outputsZero (c : QuadCircuitData F) (inputs : Nat → F) : Prop :=
  ∀ i < c.noutput, (layerValuations c inputs).getD 0 (fun _ => 0) i = 0

/-- The circuit accepts `inputs`: no assertion fails and every output wire is zero. -/
def Accepts (c : QuadCircuitData F) (inputs : Nat → F) : Prop :=
  ¬ circuitFails c inputs ∧ outputsZero c inputs

/-! ## The layer-valuation specification -/

/-- The `l`-th entry of `valuationsAux layers below` is `evalLayer (layers[l])` applied to
    the valuation of the layer beneath it (or `below` for the deepest layer). -/
theorem valuationsAux_spec (layers : List (LayerData F)) (below : Nat → F) (l : Nat)
    (hl : l < layers.length) :
    (valuationsAux layers below).getD l (fun _ => 0) =
      evalLayer (layers.get ⟨l, hl⟩)
        (if h : l + 1 < layers.length then
           (valuationsAux layers below).getD (l + 1) (fun _ => 0)
         else below) := by
  induction layers generalizing below l with
  | nil => exact (Nat.not_lt_zero _ hl).elim
  | cons layer rest ih =>
      cases l with
      | zero =>
          cases rest with
          | nil => simp [valuationsAux]
          | cons r rest' => simp [valuationsAux, List.getD]
      | succ l =>
          cases rest with
          | nil => simp at hl
          | cons r rest' =>
              simp [valuationsAux, List.getD]
              have hl' : l < (r :: rest').length := by
                have : (layer :: r :: rest').length = (r :: rest').length + 1 := by simp
                omega
              have := ih below l hl'
              simpa [valuationsAux, List.getD] using this

/-- The `l`-th entry of `layerValuations` is `evalLayer (layers[l])` applied to the input
    valuation of layer `l`. -/
theorem layerValuation_spec (c : QuadCircuitData F) (inputs : Nat → F) (l : Nat)
    (hl : l < c.layers.length) :
    (layerValuations c inputs).getD l (fun _ => 0) =
      evalLayer (c.layers.get ⟨l, hl⟩) (c.inputValuation inputs l) := by
  dsimp [layerValuations]
  rw [valuationsAux_spec c.layers inputs l hl]
  congr 1
  ext i
  dsimp [QuadCircuitData.inputValuation, wireValue]
  by_cases hcond : l + 1 < c.layers.length
  · simp [hcond, layerValuations]
  · have heq : l + 1 = c.layers.length := by omega
    simp [hcond, heq]

/-! ## DAG data and interpretation -/

/-- A term of a `sum` node: `k · v[w0] · v[w1]`, with `w0`, `w1` node indices. -/
structure SumTerm (F : Type) where
  k : F
  w0 : Nat
  w1 : Nat

/-- A node of the quad DAG. `input pos` reads input position `pos`; `sum` computes a sum of
    products of operand nodes; `assert0 w` records that node `w` must be zero (last-layer
    assertions only; mid-circuit assertions are materialized `sum` nodes). -/
inductive DagNode (F : Type) where
  | input (pos : Nat)
  | sum (terms : List (SumTerm F))
  | assert0 (w : Nat)

/-- Value of a single node given the values `vals` of all earlier nodes
    (`vals.getD i 0` is the value of node `i`). -/
def nodeValue (inputs : Nat → F) (vals : List F) : DagNode F → F
  | .input pos => inputs pos
  | .sum terms =>
      terms.foldl
        (fun acc t => acc + t.k * vals.getD t.w0 0 * vals.getD t.w1 0) 0
  | .assert0 w => vals.getD w 0

/-- Fold over the DAG computing every node's value in index order. `acc` holds the values of
    the nodes processed so far, in order. -/
def interpDagAux (inputs : Nat → F) : List (DagNode F) → List F → List F
  | [], acc => acc
  | node :: rest, acc => interpDagAux inputs rest (acc ++ [nodeValue inputs acc node])

/-- Interpretation of node `n` in `dag` under circuit inputs `inputs`. -/
def interpDag (dag : List (DagNode F)) (inputs : Nat → F) (n : Nat) : F :=
  (interpDagAux inputs dag []).getD n 0

theorem interpDagAux_length (inputs : Nat → F) (dag : List (DagNode F)) (acc : List F) :
    (interpDagAux inputs dag acc).length = dag.length + acc.length := by
  induction dag generalizing acc with
  | nil => simp [interpDagAux]
  | cons node rest ih =>
      simp [interpDagAux, ih]
      omega

/-- The fold only appends: the first `acc.length` entries are exactly `acc`. -/
theorem interpDagAux_take_left (inputs : Nat → F) (dag : List (DagNode F)) (acc : List F) :
    (interpDagAux inputs dag acc).take acc.length = acc := by
  induction dag generalizing acc with
  | nil => simp [interpDagAux]
  | cons node rest ih =>
      simp [interpDagAux]
      have := ih (acc ++ [nodeValue inputs acc node])
      have hlen_append : (acc ++ [nodeValue inputs acc node]).length = acc.length + 1 := by simp
      have hmin : min acc.length (acc ++ [nodeValue inputs acc node]).length = acc.length :=
        min_eq_left (calc
          acc.length ≤ acc.length + 1 := Nat.le_add_right _ _
          _ = (acc ++ [nodeValue inputs acc node]).length := by rw [hlen_append])
      have htake_eq : ((interpDagAux inputs rest (acc ++ [nodeValue inputs acc node])).take
          ((acc ++ [nodeValue inputs acc node]).length)).take acc.length =
        (interpDagAux inputs rest (acc ++ [nodeValue inputs acc node])).take acc.length := by
        rw [List.take_take, hmin]
      calc (interpDagAux inputs rest (acc ++ [nodeValue inputs acc node])).take acc.length
          = ((interpDagAux inputs rest (acc ++ [nodeValue inputs acc node])).take
              ((acc ++ [nodeValue inputs acc node]).length)).take acc.length := by rw [htake_eq]
          _ = (acc ++ [nodeValue inputs acc node]).take acc.length := by rw [this]
          _ = acc := List.take_left

/-- The fold is associative: processing `a ++ b` from `acc` is the same as processing `a`
    and then `b` from the result. -/
theorem interpDagAux_append (inputs : Nat → F) (a b : List (DagNode F)) (acc : List F) :
    interpDagAux inputs (a ++ b) acc = interpDagAux inputs b (interpDagAux inputs a acc) := by
  induction a generalizing acc with
  | nil => simp [interpDagAux]
  | cons node rest ih =>
      simp only [interpDagAux, List.cons_append]
      exact ih (acc ++ [nodeValue inputs acc node])

/-- After processing the first `n` nodes of `dag`, the accumulator is the prefix of length
    `acc.length + n` of the full result. -/
theorem interpDagAux_take_step (inputs : Nat → F) (dag : List (DagNode F)) (acc : List F)
    (n : Nat) (hn : n ≤ dag.length) :
    (interpDagAux inputs dag acc).take (acc.length + n) =
      interpDagAux inputs (dag.take n) acc := by
  have hsplit : dag.take n ++ dag.drop n = dag := List.take_append_drop n dag
  have hX : interpDagAux inputs dag acc =
      interpDagAux inputs (dag.drop n) (interpDagAux inputs (dag.take n) acc) := by
    calc
      interpDagAux inputs dag acc
          = interpDagAux inputs (dag.take n ++ dag.drop n) acc := by rw [hsplit]
      _ = interpDagAux inputs (dag.drop n) (interpDagAux inputs (dag.take n) acc) := by
        rw [interpDagAux_append]
  rw [hX]
  have hlen : (interpDagAux inputs (dag.take n) acc).length = acc.length + n := by
    rw [interpDagAux_length, List.length_take, min_eq_left hn]
    omega
  have htake := interpDagAux_take_left inputs (dag.drop n) (interpDagAux inputs (dag.take n) acc)
  -- htake: (interpDagAux ...).take (interpDagAux ...).length = interpDagAux ...
  -- Goal: (interpDagAux ...).take (acc.length + n) = interpDagAux ...
  -- hlen: (interpDagAux ...).length = acc.length + n
  simpa [hlen] using htake

/-- The value computed for node `n` is `nodeValue` applied to the values of the preceding
    nodes. Fundamental correctness statement of the DAG fold. -/
theorem interpDagAux_nth_gen (inputs : Nat → F) (dag : List (DagNode F)) (acc : List F)
    (n : Nat) (hn : n < dag.length) :
    (interpDagAux inputs dag acc).getD (acc.length + n) 0 =
      nodeValue inputs ((interpDagAux inputs dag acc).take (acc.length + n))
        (dag.get ⟨n, hn⟩) := by
  induction dag generalizing acc n with
  | nil => exact (Nat.not_lt_zero _ hn).elim
  | cons node rest ih =>
      let v := nodeValue inputs acc node
      have hcons : interpDagAux inputs (node :: rest) acc =
          interpDagAux inputs rest (acc ++ [v]) := by
        simp [interpDagAux, v]
      cases n with
      | zero =>
          have htake : (interpDagAux inputs (node :: rest) acc).take acc.length = acc := by
            rw [hcons]
            let X := interpDagAux inputs rest (acc ++ [v])
            have htake_left := interpDagAux_take_left inputs rest (acc ++ [v])
            have hlen_append : (acc ++ [v]).length = acc.length + 1 := by simp
            have hle : acc.length ≤ (acc ++ [v]).length := by
              rw [hlen_append]
              omega
            have hXlen : X.take (acc ++ [v]).length = acc ++ [v] := htake_left
            calc X.take acc.length
                = X.take (min acc.length (acc ++ [v]).length) := by rw [min_eq_left hle]
                _ = (X.take (acc ++ [v]).length).take acc.length :=
                  (List.take_take (i := acc.length) (j := (acc ++ [v]).length) (l := X)).symm
                _ = (acc ++ [v]).take acc.length := by rw [hXlen]
                _ = acc := List.take_left
          have hgetD : (interpDagAux inputs (node :: rest) acc).getD acc.length 0 = v := by
            rw [hcons]
            have hlen : acc.length < (interpDagAux inputs rest (acc ++ [v])).length := by
              rw [interpDagAux_length]
              have : (acc ++ [v]).length = acc.length + 1 := by simp
              omega
            have hgetD' := getD_take_of_lt (interpDagAux inputs rest (acc ++ [v])) acc.length 0 hlen
            rw [hgetD']
            have htake_left := interpDagAux_take_left inputs rest (acc ++ [v])
            have hlen_append : (acc ++ [v]).length = acc.length + 1 := by simp
            rw [hlen_append] at htake_left
            rw [htake_left]
            exact getD_append_last acc v 0
          have hget0 : (node :: rest).get ⟨0, hn⟩ = node := by simp
          simp [add_zero, hget0, htake]
          -- goal: X[acc.length]?.getD 0 = nodeValue inputs acc node
          -- hgetD: X.getD acc.length 0 = v
          -- These are the same under the hood
          simpa using hgetD
      | succ n =>
          have hn' : n < rest.length :=
            Nat.lt_of_succ_lt_succ (by simpa [List.length] using hn)
          rw [hcons]
          have hlen : (acc ++ [v]).length = acc.length + 1 := by simp
          have := ih (acc ++ [v]) n hn'
          -- `this` is the statement for `rest`, acc `acc ++ [v]`, index `n`.
          -- Rewrite its LHS/RHS to match the goal.
          have hgoal : acc.length + n.succ = (acc ++ [v]).length + n := by omega
          rw [hgoal] at *
          simpa [List.length, hlen] using this

/-! ## Wire map and valid scheduling -/

/-- A wire map assigns each DAG node to at most one circuit wire `(layer, index)`. Input
    nodes sit at the pseudo-layer `nlayers` with their input position. -/
abbrev WireMap := Nat → Option (Nat × Nat)

/-- Value of an operand node read from the layer-beneath valuation `below`: `below i` when
    the operand is wired at `expectedLayer`, and `0` otherwise. -/
def operandVal (wireMap : WireMap) (below : Nat → F) (expectedLayer : Nat) (w : Nat) : F :=
  match wireMap w with
  | some (L, i) => if L = expectedLayer then below i else 0
  | none => 0

/-- The DAG sum of node `n` evaluated against the layer-beneath valuation `below`. -/
def nodeSum (dag : List (DagNode F)) (wireMap : WireMap) (below : Nat → F)
    (expectedLayer : Nat) (n : Nat) : F :=
  match dag.getD n (.input 0) with
  | .sum terms =>
      terms.foldl
        (fun acc t =>
          acc + t.k * operandVal wireMap below expectedLayer t.w0
                * operandVal wireMap below expectedLayer t.w1) 0
  | _ => 0

/-- A scheduling of the DAG into the layered circuit, valid for circuit inputs `inputs`.

    `sum_local` is the *local simulation*; Phase 2 derives it from the sidecar's syntactic
    term-for-term reproduction check (`build_sidecar::check_dag_reproduces_circuit`).
    `sum_operands_lt` records that operands reference earlier nodes, which the compiler
    guarantees by construction (`walk_eltw` pushes operands before parents).

    `input_wire` carries the bound `n < dag.length` because `List.getD` is total: an
    out-of-range index returns the default node `.input 0`, so without the bound the field
    would demand a wire for every index past the end of the DAG and no scheduling could
    satisfy it.

    `map_inrange` confines the wire map to actual DAG nodes. Without it the structure is
    inconsistent with `simulation`: a node index past the end of `dag` interprets to `0`
    (`interpDag` is total), yet a wire map sending it to the input pseudo-layer would claim
    it equals `inputs g`. `build_sidecar` emits exactly one wire slot per node
    (`cert.rs:107-111`), so this holds of every sidecar by construction.

    `wire_inj` says no two DAG nodes share a circuit wire. `simulation` does not need it, but
    it is what makes `sum_local` *satisfiable*: `evalLayer` sums every layer term whose output
    is `g`, so if two sum nodes were mapped to the same `(L, g)` the layer value would be the
    sum of both nodes' terms and could equal neither node's `nodeSum`. The scheduler
    guarantees it by handing out one wire id per sum node per depth
    (`scheduler.rs::assign_wire_ids`); Phase 2 must check it on the dumped map, since it is a
    precondition of the term-for-term reproduction argument rather than a consequence of it. -/
structure ValidScheduling (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) : Prop where
  map_inrange : ∀ n L g, wireMap n = some (L, g) → n < dag.length
  wire_inj : ∀ m n L g, wireMap m = some (L, g) → wireMap n = some (L, g) → m = n
  input_wire : ∀ n pos, n < dag.length → dag.getD n (.input 0) = .input pos →
    wireMap n = some (c.layers.length, pos)
  assert0_nowire : ∀ n w, dag.getD n (.input 0) = .assert0 w → wireMap n = none
  sum_inrange : ∀ n L g terms, dag.getD n (.input 0) = .sum terms → wireMap n = some (L, g) →
    L < c.layers.length
  sum_operands : ∀ n L g terms t, dag.getD n (.input 0) = .sum terms →
    wireMap n = some (L, g) → t ∈ terms →
    (∃ i0, wireMap t.w0 = some (L + 1, i0)) ∧ (∃ i1, wireMap t.w1 = some (L + 1, i1))
  sum_operands_lt : ∀ n terms, dag.getD n (.input 0) = .sum terms →
    ∀ t ∈ terms, t.w0 < n ∧ t.w1 < n
  sum_local : ∀ n L g terms,
    dag.getD n (.input 0) = .sum terms → wireMap n = some (L, g) →
    evalLayer (c.layerAt L) (c.inputValuation inputs L) g =
      nodeSum dag wireMap (c.inputValuation inputs L) (L + 1) n

/-! ## Field lemma: the mid-circuit assertion mechanism -/

/-- Over a field, `w² = 0` iff `w = 0`. Justifies modelling a materialized assertion term
    `(g, w, w, 0)` as the constraint `v[w] = 0`. -/
theorem sq_eq_zero {w : F} : w * w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have := mul_eq_zero.mp h
    tauto
  · rintro rfl
    simp

/-! ## The simulation theorem -/

/-- The value of node `n` is `nodeValue` applied to the values of the nodes before it,
    phrased with `getD` so it composes with `ValidScheduling`'s node lookups. -/
theorem interpDag_getD (inputs : Nat → F) (dag : List (DagNode F)) (n : Nat)
    (hn : n < dag.length) :
    interpDag dag inputs n =
      nodeValue inputs ((interpDagAux inputs dag []).take n) (dag.getD n (.input 0)) := by
  have h := interpDagAux_nth_gen inputs dag [] n hn
  simp only [List.length_nil, Nat.zero_add] at h
  show (interpDagAux inputs dag []).getD n 0 = _
  rw [h]
  exact congrArg _ (List.getD_eq_get dag (.input 0) ⟨n, hn⟩).symm

/-- Reading an earlier node's value out of the running accumulator is the same as reading it
    out of the finished list. -/
private lemma interpDag_take (inputs : Nat → F) (dag : List (DagNode F)) (n w : Nat)
    (hw : w < n) : ((interpDagAux inputs dag []).take n).getD w 0 = interpDag dag inputs w := by
  set X := interpDagAux inputs dag [] with hX
  by_cases hwX : w < X.length
  · have hlen : w < (X.take n).length := by
      have h := List.length_take (l := X) (i := n)
      omega
    calc (X.take n).getD w 0
        = ((X.take n).take (w + 1)).getD w 0 := getD_take_of_lt (X.take n) w 0 hlen
      _ = (X.take (w + 1)).getD w 0 := by
          rw [List.take_take, min_eq_left (by omega : w + 1 ≤ n)]
      _ = X.getD w 0 := (getD_take_of_lt X w 0 hwX).symm
  · have h1 : (X.take n).getD w 0 = 0 :=
      List.getD_eq_default _ _ (by
        have := List.length_take (l := X) (i := n)
        omega)
    have h2 : X.getD w 0 = 0 := List.getD_eq_default _ _ (by omega)
    rw [h1]
    exact h2.symm

/-- A sum node's interpretation is the fold of its terms over the interpretations of its
    operands (which reference earlier nodes). -/
theorem interpDag_sum (inputs : Nat → F) (dag : List (DagNode F)) (n : Nat) (terms)
    (hget : dag.getD n (.input 0) = .sum terms)
    (hlt : ∀ t ∈ terms, t.w0 < n ∧ t.w1 < n) :
    interpDag dag inputs n =
      terms.foldl
        (fun acc t => acc + t.k * interpDag dag inputs t.w0 * interpDag dag inputs t.w1) 0 := by
  by_cases hn : n < dag.length
  · rw [interpDag_getD inputs dag n hn, hget]
    show (terms.foldl (fun acc t => acc + t.k
        * ((interpDagAux inputs dag []).take n).getD t.w0 0
        * ((interpDagAux inputs dag []).take n).getD t.w1 0) 0) = _
    refine foldl_congr_mem _ _ terms (fun b t ht => ?_) 0
    rw [interpDag_take inputs dag n t.w0 (hlt t ht).1,
        interpDag_take inputs dag n t.w1 (hlt t ht).2]
  · rw [List.getD_eq_default dag (.input 0) (by omega)] at hget
    exact absurd hget (by simp)

/-- Under a valid scheduling, the layer value of the wire a node is mapped to equals the DAG
    interpretation of that node. This is the lemma that absorbs every compiler optimization:
    the dumped DAG is self-interpreting, and only the endpoint correspondence (checked by the
    sidecar) is required.

    The induction is on the node index: `sum_operands_lt` puts every operand strictly earlier,
    `sum_operands` puts it one layer below, and the induction hypothesis converts the operand's
    *wire* value at layer `L + 1` (or the circuit input, when `L` is the deepest layer) into its
    *DAG* interpretation. `sum_local` then supplies the one endpoint fact the sidecar checks. -/
theorem simulation (c : QuadCircuitData F) (dag : List (DagNode F)) (wireMap : WireMap)
    (inputs : Nat → F) (vs : ValidScheduling c dag wireMap inputs) :
    ∀ n L g, wireMap n = some (L, g) →
      (L = c.layers.length → interpDag dag inputs n = inputs g) ∧
      (L < c.layers.length → wireValue c inputs L g = interpDag dag inputs n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L g hmap
      have hn : n < dag.length := vs.map_inrange n L g hmap
      cases hnode : dag.getD n (.input 0) with
      | input pos =>
          have hin := vs.input_wire n pos hn hnode
          rw [hin] at hmap
          obtain ⟨hL, hg⟩ := Prod.mk.inj (Option.some.inj hmap)
          subst hg
          constructor
          · intro _
            rw [interpDag_getD inputs dag n hn, hnode]
            rfl
          · intro hlt
            omega
      | assert0 w =>
          have hnowire := vs.assert0_nowire n w hnode
          rw [hnowire] at hmap
          exact absurd hmap (by simp)
      | sum terms =>
          constructor
          · intro hL
            have := vs.sum_inrange n L g terms hnode hmap
            omega
          · intro hlt
            -- Every operand's layer-beneath value is its DAG interpretation.
            have operand_eq : ∀ w, w < n → ∀ i, wireMap w = some (L + 1, i) →
                operandVal wireMap (c.inputValuation inputs L) (L + 1) w
                  = interpDag dag inputs w := by
              intro w hw i hwi
              have ihw := ih w hw (L + 1) i hwi
              simp only [operandVal, hwi]
              by_cases hcond : L + 1 < c.layers.length
              · simp only [QuadCircuitData.inputValuation, if_pos hcond]
                exact ihw.2 hcond
              · have heq : L + 1 = c.layers.length := by omega
                simp only [QuadCircuitData.inputValuation, if_neg hcond]
                exact (ihw.1 heq).symm
            -- Hence the node's local sum is its DAG interpretation.
            have hkey : nodeSum dag wireMap (c.inputValuation inputs L) (L + 1) n
                = interpDag dag inputs n := by
              rw [interpDag_sum inputs dag n terms hnode (vs.sum_operands_lt n terms hnode)]
              simp only [nodeSum, hnode]
              refine foldl_congr_mem _ _ terms (fun b t ht => ?_) 0
              obtain ⟨⟨i0, h0⟩, ⟨i1, h1⟩⟩ := vs.sum_operands n L g terms t hnode hmap ht
              rw [operand_eq t.w0 (vs.sum_operands_lt n terms hnode t ht).1 i0 h0,
                  operand_eq t.w1 (vs.sum_operands_lt n terms hnode t ht).2 i1 h1]
            calc wireValue c inputs L g
                = (layerValuations c inputs).getD L (fun _ => 0) g := by
                  simp only [wireValue, dif_pos hlt]
              _ = evalLayer (c.layers.get ⟨L, hlt⟩) (c.inputValuation inputs L) g := by
                  rw [layerValuation_spec c inputs L hlt]
              _ = evalLayer (c.layerAt L) (c.inputValuation inputs L) g := by
                  rw [QuadCircuitData.layerAt_mem c L hlt]
              _ = nodeSum dag wireMap (c.inputValuation inputs L) (L + 1) n :=
                  vs.sum_local n L g terms hnode hmap
              _ = interpDag dag inputs n := hkey


/-! ## Gate table: the arithmetization the sumcheck protocol extends

`formal/lfzk` states its layer relation over a **gate table** `gate_v : ℕ → ℕ → ℕ → F`, of which
`quadMle` is the multilinear extension. The sidecar ships a **term list**. This section builds
the table from the terms and proves that the two agree — the first half of discharging
`LayeredCircuit.layer_rel`.

The table entry is a *sum*, not a lookup: canonical order permits several terms sharing
`(g, h0, h1)` because `compare_term` (`core/proto/src/layer.rs:355`) tie-breaks on the constant
after `(h0, h1)` and `g`. Measured on the ECDSA2 circuit there are no such collisions, but
nothing in the compiler forbids them, so the model must sum.
-/

/-- Coefficient of `vin[j] · vin[k]` in output wire `g`, summed over all terms carrying it. -/
def gateOf (layer : LayerData F) (g j k : Nat) : F :=
  (layer.terms.map (fun t => if t.g = g ∧ t.h0 = j ∧ t.h1 = k then t.k else 0)).sum

/-- A conditional `foldl` accumulating into `acc` is `acc` plus the sum of the guarded values. -/
private lemma foldl_cond_eq_sum (ts : List (QuadTerm F)) (p : QuadTerm F → Prop)
    [DecidablePred p] (f : QuadTerm F → F) (acc : F) :
    ts.foldl (fun a t => if p t then a + f t else a) acc
      = acc + (ts.map (fun t => if p t then f t else 0)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      by_cases hp : p t
      · rw [if_pos hp, ih, if_pos hp]; ring
      · rw [if_neg hp, ih, if_neg hp]; ring

/-- `evalLayer` in summation form. -/
theorem evalLayer_eq_listSum (layer : LayerData F) (vin : Nat → F) (g : Nat) :
    evalLayer layer vin g
      = (layer.terms.map (fun t => if t.g = g then t.k * vin t.h0 * vin t.h1 else 0)).sum := by
  dsimp [evalLayer]
  rw [foldl_cond_eq_sum (p := fun t => t.g = g)
        (f := fun t => t.k * vin t.h0 * vin t.h1) (acc := 0)]
  simp

/-- One term's contribution, seen through the gate table: the double sum over the wire indices
    collapses onto that term's own `(h0, h1)`. -/
private lemma single_term_gate (t : QuadTerm F) (vin : Nat → F) (g nw : Nat)
    (h0lt : t.h0 < nw) (h1lt : t.h1 < nw) :
    ∑ j ∈ Finset.range nw, ∑ k ∈ Finset.range nw,
        (if t.g = g ∧ t.h0 = j ∧ t.h1 = k then t.k else 0) * vin j * vin k
      = if t.g = g then t.k * vin t.h0 * vin t.h1 else 0 := by
  by_cases hg : t.g = g
  · rw [if_pos hg, Finset.sum_eq_single t.h0]
    · rw [Finset.sum_eq_single t.h1]
      · simp [hg]
      · intro k _ hk; simp [hg, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_range.mpr h1lt) h
    · intro j _ hj
      refine Finset.sum_eq_zero (fun k _ => ?_)
      simp [hg, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_range.mpr h0lt) h
  · rw [if_neg hg]
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => ?_))
    simp [hg]

/-- The list-level induction behind `evalLayer_eq_gateSum`. -/
private theorem listSum_eq_gateSum (vin : Nat → F) (g nw : Nat) :
    ∀ ts : List (QuadTerm F), (∀ t ∈ ts, t.h0 < nw ∧ t.h1 < nw) →
      (ts.map (fun t => if t.g = g then t.k * vin t.h0 * vin t.h1 else 0)).sum
        = ∑ j ∈ Finset.range nw, ∑ k ∈ Finset.range nw,
            (ts.map (fun t => if t.g = g ∧ t.h0 = j ∧ t.h1 = k then t.k else 0)).sum
              * vin j * vin k := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
      intro hb
      have hbt : t.h0 < nw ∧ t.h1 < nw := hb t List.mem_cons_self
      have hbs : ∀ t' ∈ ts, t'.h0 < nw ∧ t'.h1 < nw :=
        fun t' ht' => hb t' (List.mem_cons_of_mem t ht')
      simp only [List.map_cons, List.sum_cons]
      have hsplit : ∀ j k : Nat,
          ((if t.g = g ∧ t.h0 = j ∧ t.h1 = k then t.k else 0)
              + (ts.map (fun t' => if t'.g = g ∧ t'.h0 = j ∧ t'.h1 = k then t'.k else 0)).sum)
            * vin j * vin k
          = (if t.g = g ∧ t.h0 = j ∧ t.h1 = k then t.k else 0) * vin j * vin k
              + (ts.map (fun t' => if t'.g = g ∧ t'.h0 = j ∧ t'.h1 = k then t'.k else 0)).sum
                  * vin j * vin k := by
        intro j k; ring
      simp only [hsplit, Finset.sum_add_distrib]
      rw [single_term_gate t vin g nw hbt.1 hbt.2, ih hbs]

/-- **The arithmetization lemma.** Layer evaluation is the gate-table quadratic form. This is
    the statement `formal/lfzk` needs in order to read the sidecar's terms as its `gate_v`;
    the remaining step to `LayeredCircuit.layer_rel` is the multilinear extension, which lives
    on the `lfzk` side (`quadMle`, `eq_mle_basis`).

    `hb` — every term's operand indices lie below `nw` — is a decidable sidecar check, and the
    Rust evaluator would index out of bounds without it (`eval.rs:137`). -/
theorem evalLayer_eq_gateSum (layer : LayerData F) (vin : Nat → F) (g nw : Nat)
    (hb : ∀ t ∈ layer.terms, t.h0 < nw ∧ t.h1 < nw) :
    evalLayer layer vin g
      = ∑ j ∈ Finset.range nw, ∑ k ∈ Finset.range nw, gateOf layer g j k * vin j * vin k := by
  rw [evalLayer_eq_listSum]
  exact listSum_eq_gateSum vin g nw layer.terms hb

/-! ## Template schemas

Measured on ECDSA2, the 1,048 assertion sub-DAGs share only **52 structural templates**
(20.2×), with 256 instances each of `valid_index`, `slice_wx`, `slice_wy`, `slice_wz`. The
expensive part of a meaning lemma is unfolding `interpDag` and normalising with `ring`; doing
that once per *template* rather than once per *instance* is the whole saving.

The instances cannot be indexed arithmetically — measured, their node indices, input
positions and leaf counts are all irregular, because `assign_wire_ids` re-sorts every layer
and the records are ordered by wire coordinate. So a schema is **parameterised by its leaf
nodes** rather than by a loop index; each instance then supplies its own leaves and discharges
the structural hypothesis by `rfl`. Irregularity costs nothing under this framing.

`interpDag_sum` already gives the one-level unfolding generically; `interpDag_input` closes
the leaves. -/

/-- A leaf: an input node interprets to its input. -/
theorem interpDag_input (dag : List (DagNode F)) (inputs : Nat → F) (n pos : Nat)
    (hn : n < dag.length) (h : dag.getD n (.input 0) = .input pos) :
    interpDag dag inputs n = inputs pos := by
  rw [interpDag_getD inputs dag n hn, h]
  rfl

/-! ## The sparse quad relation

`lfzk` states its layer relation over a **dense** gate table indexed by `(g, j, k)`, of which
`quadMle` is the multilinear extension. Materializing that is both expensive and, in one case,
wrong.

*Expensive*: `gateOf` scans the whole term list per cell, and the double sum runs over `nw²`
cells. ECDSA2's widest layer has `logw = 13`, so `nw² ≈ 67M` cells over a ~20k-term list.

*Wrong*: `prepV v b = if v = 0 then b else v` is **not additive**, and the runtime applies it
per term (`quad.h:L213`). A dense table must first sum the coefficients of terms sharing
`(g, h0, h1)`; two such terms with `k = 5` and `k = -5` sum to `0`, and `prepV 0 b = b` — a
*beta-weighted assert-zero gate* — whereas the faithful per-term reading gives
`prepV 5 b + prepV (-5) b = 0`. The two agree exactly when no `(g, h0, h1)` repeats. ECDSA2
has no such duplicate as measured, but nothing in the compiler forbids one, because
`compare_term` (`core/proto/src/layer.rs:355`) tie-breaks on the constant.

So the sparse form below is the primary object: **one summand per term**, O(nterms), faithful
unconditionally. `LayeredCircuit.Quad` is a structure *field*, so it can be instantiated with
this directly and `quadMle` never has to be materialized.

The equality-basis functions are parameters rather than `lfzk`'s `eq_mle_basis`, so `quadcert`
need not depend on `lfzk`; instantiate them at the bridge.
-/

/-- Sparse multilinear extension of a layer's quad relation: one summand per term. `prep`
    stands for `prepV · b` at the layer's `beta`. -/
def sparseQuad {V : Type} (layer : LayerData F) (prep : F → F)
    (eqv eqw : Nat → V → F) (gv lv rv : V) : F :=
  (layer.terms.map (fun t => prep t.k * eqv t.g gv * eqw t.h0 lv * eqw t.h1 rv)).sum

/-- **At boolean points the sparse form collapses to the terms of one cell.** No `nw²` sum
    appears, and duplicate `(g, h0, h1)` coefficients stay separate — which is what keeps
    `prep` applied per term. -/
theorem sparseQuad_boolean {V : Type} (layer : LayerData F) (prep : F → F)
    (eqv eqw : Nat → V → F) (gv lv rv : V) (g j k : Nat)
    (hv : ∀ i, eqv i gv = if i = g then 1 else 0)
    (hl : ∀ i, eqw i lv = if i = j then 1 else 0)
    (hr : ∀ i, eqw i rv = if i = k then 1 else 0) :
    sparseQuad layer prep eqv eqw gv lv rv
      = (layer.terms.map
          (fun t => if t.g = g ∧ t.h0 = j ∧ t.h1 = k then prep t.k else 0)).sum := by
  simp only [sparseQuad]
  congr 1
  refine List.map_congr_left (fun t _ => ?_)
  rw [hv, hl, hr]
  by_cases h1 : t.g = g <;> by_cases h2 : t.h0 = j <;> by_cases h3 : t.h1 = k <;>
    simp [h1, h2, h3]

/-- With `prep = id` the collapse is exactly the dense gate-table entry — so the sparse form
    refines `gateOf` rather than replacing its meaning. -/
theorem sparseQuad_id_eq_gateOf {V : Type} (layer : LayerData F)
    (eqv eqw : Nat → V → F) (gv lv rv : V) (g j k : Nat)
    (hv : ∀ i, eqv i gv = if i = g then 1 else 0)
    (hl : ∀ i, eqw i lv = if i = j then 1 else 0)
    (hr : ∀ i, eqw i rv = if i = k then 1 else 0) :
    sparseQuad layer id eqv eqw gv lv rv = gateOf layer g j k :=
  sparseQuad_boolean layer id eqv eqw gv lv rv g j k hv hl hr

/-- **The layer relation, sparsely.** Layer evaluation is the quadratic form of the sparse
    relation over the boolean points — the shape `LayeredCircuit.layer_rel` needs, with no
    dense table anywhere. -/
theorem evalLayer_eq_sparseSum {V : Type} (layer : LayerData F) (nw : Nat)
    (eqv eqw : Nat → V → F) (gv : V) (pt : Nat → V) (vin : Nat → F) (g : Nat)
    (hv : ∀ i, eqv i gv = if i = g then 1 else 0)
    (hpt : ∀ i m, eqw i (pt m) = if i = m then 1 else 0)
    (hb : ∀ t ∈ layer.terms, t.h0 < nw ∧ t.h1 < nw) :
    evalLayer layer vin g
      = ∑ j ∈ Finset.range nw, ∑ k ∈ Finset.range nw,
          sparseQuad layer id eqv eqw gv (pt j) (pt k) * vin j * vin k := by
  rw [evalLayer_eq_gateSum layer vin g nw hb]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [sparseQuad_id_eq_gateOf layer eqv eqw gv (pt j) (pt k) g j k hv
    (fun i => hpt i j) (fun i => hpt i k)]

/-! ## Grouped layer evaluation — the route to `sum_local` at scale

`evalLayer layer vin g` folds over the layer's **entire** term list filtering on `t.g = g`.
Discharging `sum_local` that way costs O(nterms · nwires) — 1.2×10⁹ for ECDSA2.

The fix is to reason about a *grouped* view of the layer: a function `groupOf : Nat → List
QuadTerm` giving each wire its own terms. Two facts relate it to the deployed circuit — that
the groups flatten to a permutation of the canonical term list, and that each group is
homogeneous in `g` — and both are checkable data properties, established once per layer
rather than once per wire.

`evalLayer_eq_foldGroup` is then a *generic* theorem: instantiating it at a wire is O(1), so
the per-node cost drops to looking up `groupOf g` (a bisection, O(log n)) and comparing that
group with the node's own term list. -/

/-- The value a homogeneous group of terms contributes to its wire. -/
def foldGroup (ts : List (QuadTerm F)) (vin : Nat → F) : F :=
  (ts.map (fun t => t.k * vin t.h0 * vin t.h1)).sum

private lemma sum_map_flatMap {α : Type} (f : Nat → List α) (h : α → F) (l : List Nat) :
    ((l.flatMap f).map h).sum = (l.map (fun a => ((f a).map h).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private lemma sum_map_eq_zero {α : Type} (l : List α) (h : α → F)
    (hz : ∀ a ∈ l, h a = 0) : (l.map h).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, hz a (by simp)]
      rw [ih (fun a' ha' => hz a' (by simp [ha']))]
      simp

private lemma sum_range_indicator (n g : Nat) (v : Nat → F) :
    ((List.range n).map (fun i => if i = g then v i else 0)).sum = if g < n then v g else 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases h : g < m
      · have hm : ¬ (m = g) := by omega
        have hs : g < m + 1 := by omega
        simp [h, hm, hs]
      · by_cases h2 : g = m
        · subst h2
          simp [h]
        · have hns : ¬ (g < m + 1) := by omega
          have hm : ¬ (m = g) := fun hh => h2 hh.symm
          simp [h, hns, hm]

/-- **Grouped layer evaluation.** Under a grouping that flattens to a permutation of the
    layer's terms and is homogeneous in the output wire, a wire's value is exactly its own
    group's fold. Generic in the layer, so applying it at a wire costs nothing. -/
theorem evalLayer_eq_foldGroup (layer : LayerData F) (nw : Nat)
    (groupOf : Nat → List (QuadTerm F)) (vin : Nat → F) (g : Nat)
    (hperm : layer.terms.Perm ((List.range nw).flatMap groupOf))
    (hhom : ∀ i, ∀ t ∈ groupOf i, t.g = i) (hg : g < nw) :
    evalLayer layer vin g = foldGroup (groupOf g) vin := by
  rw [evalLayer_eq_listSum, (hperm.map _).sum_eq, sum_map_flatMap]
  have key : ∀ i,
      ((groupOf i).map (fun t => if t.g = g then t.k * vin t.h0 * vin t.h1 else 0)).sum
        = if i = g then foldGroup (groupOf i) vin else 0 := by
    intro i
    by_cases hi : i = g
    · subst hi
      rw [if_pos rfl]
      simp only [foldGroup]
      congr 1
      refine List.map_congr_left (fun t ht => ?_)
      rw [if_pos (hhom i t ht)]
    · rw [if_neg hi]
      refine sum_map_eq_zero _ _ (fun t ht => ?_)
      rw [if_neg (by rw [hhom i t ht]; exact hi)]
  simp only [key]
  rw [sum_range_indicator nw g (fun i => foldGroup (groupOf i) vin), if_pos hg]

private lemma foldl_add_eq_sum {α : Type} (f : α → F) (l : List α) (acc : F) :
    l.foldl (fun a t => a + f t) acc = acc + (l.map f).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons t l ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

/-- A layer term *realises* a DAG sum term through the wire map. The disjunction is the
    `h0 ≤ h1` canonical swap that `canonical_term` performs
    (`core/proto/src/layer.rs:342`): the layer records the operands sorted, the DAG records
    them in evaluation order, and multiplication is commutative. -/
def Realises (wireMap : WireMap) (L : Nat) (t : QuadTerm F) (u : SumTerm F) : Prop :=
  t.k = u.k ∧
    ((wireMap u.w0 = some (L + 1, t.h0) ∧ wireMap u.w1 = some (L + 1, t.h1)) ∨
     (wireMap u.w0 = some (L + 1, t.h1) ∧ wireMap u.w1 = some (L + 1, t.h0)))

private lemma map_sum_of_realises (wireMap : WireMap) (below : Nat → F) (L : Nat)
    (ts : List (QuadTerm F)) (us : List (SumTerm F))
    (hcorr : List.Forall₂ (Realises wireMap L) ts us) :
    (ts.map (fun t => t.k * below t.h0 * below t.h1)).sum
      = (us.map (fun u => u.k * operandVal wireMap below (L + 1) u.w0
                            * operandVal wireMap below (L + 1) u.w1)).sum := by
  induction hcorr with
  | nil => simp
  | cons hr _ ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      obtain ⟨hk, hw⟩ := hr
      rcases hw with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
        simp only [operandVal, h0, h1, hk, if_true, reduceIte] <;> ring

/-- **A group is its node's sum.** Given a term-by-term correspondence between a wire's group
    and its node's term list, the group's fold is the node's `nodeSum`. Purely local: the
    cost is the size of the group, not of the layer. -/
theorem foldGroup_eq_nodeSum (dag : List (DagNode F)) (wireMap : WireMap) (below : Nat → F)
    (L n : Nat) (terms : List (SumTerm F)) (ts : List (QuadTerm F))
    (hnode : dag.getD n (.input 0) = .sum terms)
    (hcorr : List.Forall₂ (Realises wireMap L) ts terms) :
    foldGroup ts below = nodeSum dag wireMap below (L + 1) n := by
  simp only [nodeSum, hnode]
  rw [foldl_add_eq_sum, zero_add]
  exact map_sum_of_realises wireMap below L ts terms hcorr

/-- **`sum_local`, assembled.** The two halves compose: grouped evaluation reduces the layer
    to one wire's group, and the correspondence reduces that group to the node. Neither step
    scans the layer. -/
theorem sum_local_of_grouping (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) (L g n nw : Nat)
    (groupOf : Nat → List (QuadTerm F)) (terms : List (SumTerm F))
    (hperm : (c.layerAt L).terms.Perm ((List.range nw).flatMap groupOf))
    (hhom : ∀ i, ∀ t ∈ groupOf i, t.g = i) (hg : g < nw)
    (hnode : dag.getD n (.input 0) = .sum terms)
    (hcorr : List.Forall₂ (Realises wireMap L) (groupOf g) terms) :
    evalLayer (c.layerAt L) (c.inputValuation inputs L) g =
      nodeSum dag wireMap (c.inputValuation inputs L) (L + 1) n := by
  rw [evalLayer_eq_foldGroup (c.layerAt L) nw groupOf _ g hperm hhom hg]
  exact foldGroup_eq_nodeSum dag wireMap _ L n terms (groupOf g) hnode hcorr

/-! ## Bridge: acceptance is exactly the named assertions

This is what the spec bridge (Phase 3) consumes. `simulation` relates *wires* to DAG nodes;
this section relates *acceptance* to the sidecar's assertion records, so that the human work
downstream is `(∀ records r, interp r.assertedNode = 0) → Spec` and nothing else.

Both directions are needed and they rest on different checks:

* `Backed` — every record is carried by a real circuit constraint. This gives
  `Accepts → assertions zero`, which is the direction ZK **soundness** needs.
* `CoversConstraints` — every circuit constraint is carried by a record. This gives
  `assertions zero → Accepts`, i.e. that there is no *unnamed* constraint on the witness.
  Without it the spec bridge would prove a theorem about a strictly weaker circuit.

Both are decidable predicates on sidecar data; neither mentions `inputs`.
-/

/-- One assertion record of the sidecar (`cert.rs::ParsedAssertion`): the DAG node whose value
    the assertion pins to zero, and the circuit wire carrying the constraint. Scope paths are
    not modelled here — they are the spec bridge's index into these records. -/
structure AssertionRec where
  assertedNode : Nat
  wireLayer : Nat
  wireIndex : Nat

/-- Wire `g` is *structurally zero*: every term feeding it is an assertion term (`k = 0`), so
    its value is `0` on every input. This is the shape of a mid-circuit assertion that the
    scheduler materialized onto the output layer, whose output constraint therefore carries no
    information about the witness. -/
def structurallyZero (layer : LayerData F) (g : Nat) : Prop :=
  ∀ t ∈ layer.terms, t.g = g → t.k = 0

theorem evalLayer_of_structurallyZero (layer : LayerData F) (vin : Nat → F) (g : Nat)
    (h : structurallyZero layer g) : evalLayer layer vin g = 0 := by
  dsimp [evalLayer]
  have key : ∀ (ts : List (QuadTerm F)), (∀ t ∈ ts, t.g = g → t.k = 0) → ∀ acc : F,
      ts.foldl (fun acc t => if t.g = g then acc + t.k * vin t.h0 * vin t.h1 else acc) acc
        = acc := by
    intro ts
    induction ts with
    | nil => intro _ acc; rfl
    | cons t ts ih =>
        intro hts acc
        have hrest : ∀ t' ∈ ts, t'.g = g → t'.k = 0 := fun t' ht' => hts t' (by simp [ht'])
        simp only [List.foldl_cons]
        by_cases hg : t.g = g
        · rw [if_pos hg]
          have hz : acc + t.k * vin t.h0 * vin t.h1 = acc := by
            rw [hts t (by simp) hg]; ring
          rw [hz]
          exact ih hrest acc
        · rw [if_neg hg]
          exact ih hrest acc
  exact key layer.terms h 0

/-- The valuation feeding layer `l` reads a wired node as that node's DAG interpretation.
    This is `simulation` packaged for the layer *beneath* `l`, covering both the case where
    that layer is a real one and the case where it is the circuit input. -/
theorem inputValuation_eq_interp (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) (vs : ValidScheduling c dag wireMap inputs)
    (l i n : Nat) (hl : l < c.layers.length) (hmap : wireMap n = some (l + 1, i)) :
    c.inputValuation inputs l i = interpDag dag inputs n := by
  have h := simulation c dag wireMap inputs vs n (l + 1) i hmap
  by_cases hcond : l + 1 < c.layers.length
  · simp only [QuadCircuitData.inputValuation, if_pos hcond]
    exact h.2 hcond
  · have heq : l + 1 = c.layers.length := by omega
    simp only [QuadCircuitData.inputValuation, if_neg hcond]
    exact (h.1 heq).symm

/-- Record `r` is **backed** by a real circuit constraint: either a materialized mid-circuit
    assertion term `(g, i, i, 0)` in layer `r.wireLayer`, or a last-layer output wire. Decidable
    on sidecar data. -/
def Backed (c : QuadCircuitData F) (wireMap : WireMap) (r : AssertionRec) : Prop :=
  (r.wireLayer < c.layers.length ∧
      ∃ i, wireMap r.assertedNode = some (r.wireLayer + 1, i) ∧
        (⟨r.wireIndex, i, i, 0⟩ : QuadTerm F) ∈ (c.layerAt r.wireLayer).terms)
    ∨ (r.wireIndex < c.noutput ∧ wireMap r.assertedNode = some (0, r.wireIndex))

/-- The records **cover** every constraint the circuit imposes: every assertion term of every
    layer, and every output wire. An output wire may instead be structurally zero, which is how
    a materialized mid-circuit assertion landing on the output layer is discharged. Decidable on
    sidecar data. -/
def CoversConstraints (c : QuadCircuitData F) (wireMap : WireMap) (recs : List AssertionRec) :
    Prop :=
  (∀ l < c.layers.length, ∀ t ∈ (c.layerAt l).terms, t.k = 0 →
      t.h0 = t.h1 ∧ ∃ r ∈ recs, wireMap r.assertedNode = some (l + 1, t.h0))
    ∧ (∀ i < c.noutput,
        (∃ r ∈ recs, wireMap r.assertedNode = some (0, i)) ∨ structurallyZero (c.layerAt 0) i)

/-- **Soundness direction.** An accepting input assignment zeroes every named assertion. This
    is the direction the ZK soundness statement consumes. -/
theorem assertions_zero_of_accepts (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) (vs : ValidScheduling c dag wireMap inputs)
    (recs : List AssertionRec) (hb : ∀ r ∈ recs, Backed c wireMap r)
    (hlayers : 0 < c.layers.length) (hacc : Accepts c inputs) :
    ∀ r ∈ recs, interpDag dag inputs r.assertedNode = 0 := by
  obtain ⟨hnf, hout⟩ := hacc
  intro r hr
  rcases hb r hr with ⟨hl, i, hmap, hterm⟩ | ⟨hi, hmap⟩
  · -- mid-circuit: the assertion term forces `v[i]² = 0`
    have hprod : c.inputValuation inputs r.wireLayer i
        * c.inputValuation inputs r.wireLayer i = 0 := by
      by_contra hne
      exact hnf ⟨r.wireLayer, hl, ⟨r.wireIndex, i, i, 0⟩, hterm, rfl, hne⟩
    have hzero : c.inputValuation inputs r.wireLayer i = 0 := sq_eq_zero.mp hprod
    rw [← inputValuation_eq_interp c dag wireMap inputs vs r.wireLayer i r.assertedNode hl hmap]
    exact hzero
  · -- last-layer: the output wire is required to be zero
    have h := (simulation c dag wireMap inputs vs r.assertedNode 0 r.wireIndex hmap).2 hlayers
    rw [← h]
    simp only [wireValue, dif_pos hlayers]
    exact hout r.wireIndex hi

/-- **Completeness direction.** If every named assertion is zero then the circuit accepts —
    i.e. the named assertions are the *only* constraints on the witness. -/
theorem accepts_of_assertions_zero (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) (vs : ValidScheduling c dag wireMap inputs)
    (recs : List AssertionRec) (hc : CoversConstraints c wireMap recs)
    (hlayers : 0 < c.layers.length)
    (hz : ∀ r ∈ recs, interpDag dag inputs r.assertedNode = 0) :
    Accepts c inputs := by
  obtain ⟨hterms, houts⟩ := hc
  constructor
  · rintro ⟨l, hl, t, ht, hk, hne⟩
    obtain ⟨hh, r, hr, hmap⟩ := hterms l hl t ht hk
    have : c.inputValuation inputs l t.h0 = 0 := by
      rw [inputValuation_eq_interp c dag wireMap inputs vs l t.h0 r.assertedNode hl hmap]
      exact hz r hr
    exact hne (by rw [← hh, this]; ring)
  · intro i hi
    have hval : (layerValuations c inputs).getD 0 (fun _ => 0) i = wireValue c inputs 0 i := by
      simp only [wireValue, dif_pos hlayers]
    rw [hval]
    rcases houts i hi with ⟨r, hr, hmap⟩ | hstruct
    · rw [(simulation c dag wireMap inputs vs r.assertedNode 0 i hmap).2 hlayers]
      exact hz r hr
    · simp only [wireValue, dif_pos hlayers]
      rw [layerValuation_spec c inputs 0 hlayers,
          ← QuadCircuitData.layerAt_mem c 0 hlayers]
      exact evalLayer_of_structurallyZero _ _ i hstruct

/-- **The bridge.** Acceptance is exactly the conjunction of the named assertions. Everything to
    the right of the `↔` is what Phase 3 reasons about; layers, wires and scheduling do not
    appear. -/
theorem accepts_iff_assertions (c : QuadCircuitData F) (dag : List (DagNode F))
    (wireMap : WireMap) (inputs : Nat → F) (vs : ValidScheduling c dag wireMap inputs)
    (recs : List AssertionRec) (hb : ∀ r ∈ recs, Backed c wireMap r)
    (hc : CoversConstraints c wireMap recs) (hlayers : 0 < c.layers.length) :
    Accepts c inputs ↔ ∀ r ∈ recs, interpDag dag inputs r.assertedNode = 0 :=
  ⟨assertions_zero_of_accepts c dag wireMap inputs vs recs hb hlayers,
   accepts_of_assertions_zero c dag wireMap inputs vs recs hc hlayers⟩

/-!
## Non-vacuity: a concrete valid scheduling

`ValidScheduling` bundles several hypotheses, `sum_local` among them, and a theorem whose
hypotheses cannot be met says nothing. This section exhibits a scheduling that satisfies all
of them, over an arbitrary field and arbitrary circuit inputs, and reads a real value back out
through `simulation`.

The circuit is the smallest one exercising both layer kinds and both assertion mechanisms:
`assert0 (a * b)`, compiled exactly as the Rust scheduler compiles it.
-/

namespace Micro

/-- DAG for `assert0 (a * b)`. Node `0` is the reserved constant `one`, nodes `1` and `2` are
    the inputs `a` and `b`, node `3` is the product, and node `4` is the *materialized*
    assertion `Sum [(0, 3, 3)]` that `scheduler.rs::materialize_assertions` emits for a
    mid-circuit assert. -/
def dag (F : Type) [Field F] : List (DagNode F) :=
  [.input 0, .input 1, .input 2, .sum [⟨1, 1, 2⟩], .sum [⟨0, 3, 3⟩]]

/-- The scheduled circuit. Layer `1` (deepest) computes `a * b` from the inputs; layer `0`
    (output) carries the assertion term `(g = 0, h0 = h1 = 0, k = 0)`. `ninput` of a layer is
    the width of the layer beneath it, as in `core_proto::Layer::nw`. -/
def circuit (F : Type) [Field F] : QuadCircuitData F where
  ninput := 3
  noutput := 1
  layers :=
    [ { ninput := 1, terms := [⟨0, 0, 0, 0⟩] },
      { ninput := 3, terms := [⟨0, 1, 2, 1⟩] } ]

/-- A sum node at depth `d` becomes a wire of proto layer `max_depth - d`; input nodes sit at
    the pseudo-layer `nlayers = 2` with their input position as index
    (`scheduler.rs::schedule`, the `node_wires` loop). -/
def wireMap : WireMap
  | 0 => some (2, 0)
  | 1 => some (2, 1)
  | 2 => some (2, 2)
  | 3 => some (1, 0)
  | 4 => some (0, 0)
  | _ => none

section Lookups
variable (F : Type) [Field F]

private lemma dag0 : (dag F).getD 0 (.input 0) = .input 0 := rfl
private lemma dag1 : (dag F).getD 1 (.input 0) = .input 1 := rfl
private lemma dag2 : (dag F).getD 2 (.input 0) = .input 2 := rfl
private lemma dag3 : (dag F).getD 3 (.input 0) = .sum [⟨1, 1, 2⟩] := rfl
private lemma dag4 : (dag F).getD 4 (.input 0) = .sum [⟨(0 : F), 3, 3⟩] := rfl

private lemma dagBig (k : Nat) : (dag F).getD (k + 5) (.input 0) = .input 0 :=
  List.getD_eq_default _ _ (by simp only [dag, List.length_cons, List.length_nil]; omega)

private lemma nlayers_eq : (circuit F).layers.length = 2 := rfl
private lemma noutput_eq : (circuit F).noutput = 1 := rfl
private lemma layer0 :
    (circuit F).layerAt 0 = { ninput := 1, terms := [⟨0, 0, 0, 0⟩] } := rfl
private lemma layer1 :
    (circuit F).layerAt 1 = { ninput := 3, terms := [⟨0, 1, 2, 1⟩] } := rfl

end Lookups

private lemma mapped_lt_five {n : Nat} {p : Nat × Nat} (h : wireMap n = some p) : n < 5 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => omega
  | (_ + 5) => simp [wireMap] at h

/-- **The scheduling is valid**, for every field and every input assignment. -/
theorem valid (F : Type) [Field F] (inputs : Nat → F) :
    ValidScheduling (circuit F) (dag F) wireMap inputs where
  map_inrange := by
    intro n L g h
    have h5 := mapped_lt_five h
    simp only [dag, List.length_cons, List.length_nil]
    omega
  wire_inj := by
    intro m n L g hm hn
    have hm5 := mapped_lt_five hm
    have hn5 := mapped_lt_five hn
    interval_cases m <;> interval_cases n <;>
      simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hm hn <;> omega
  input_wire := by
    intro n pos hn h
    match n with
    | 0 => rw [dag0] at h; injection h with hp; subst hp; rfl
    | 1 => rw [dag1] at h; injection h with hp; subst hp; rfl
    | 2 => rw [dag2] at h; injection h with hp; subst hp; rfl
    | 3 => rw [dag3] at h; simp at h
    | 4 => rw [dag4] at h; simp at h
    | (k + 5) =>
        exfalso
        simp only [dag, List.length_cons, List.length_nil] at hn
        omega
  assert0_nowire := by
    intro n w h
    match n with
    | 0 => rw [dag0] at h; simp at h
    | 1 => rw [dag1] at h; simp at h
    | 2 => rw [dag2] at h; simp at h
    | 3 => rw [dag3] at h; simp at h
    | 4 => rw [dag4] at h; simp at h
    | (k + 5) => rw [dagBig] at h; simp at h
  sum_inrange := by
    intro n L g terms h hmap
    match n with
    | 0 => rw [dag0] at h; simp at h
    | 1 => rw [dag1] at h; simp at h
    | 2 => rw [dag2] at h; simp at h
    | 3 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        rw [nlayers_eq]; omega
    | 4 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        rw [nlayers_eq]; omega
    | (k + 5) => simp [wireMap] at hmap
  sum_operands := by
    intro n L g terms t h hmap ht
    match n with
    | 0 => rw [dag0] at h; simp at h
    | 1 => rw [dag1] at h; simp at h
    | 2 => rw [dag2] at h; simp at h
    | 3 =>
        rw [dag3] at h
        injection h with hterms
        subst hterms
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap
        subst hL
        simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨⟨1, rfl⟩, ⟨2, rfl⟩⟩
    | 4 =>
        rw [dag4] at h
        injection h with hterms
        subst hterms
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap
        subst hL
        simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
    | (k + 5) => simp [wireMap] at hmap
  sum_operands_lt := by
    intro n terms h t ht
    match n with
    | 0 => rw [dag0] at h; simp at h
    | 1 => rw [dag1] at h; simp at h
    | 2 => rw [dag2] at h; simp at h
    | 3 =>
        rw [dag3] at h; injection h with hterms; subst hterms
        simp only [List.mem_singleton] at ht; subst ht
        simp
    | 4 =>
        rw [dag4] at h; injection h with hterms; subst hterms
        simp only [List.mem_singleton] at ht; subst ht
        simp
    | (k + 5) => rw [dagBig] at h; simp at h
  sum_local := by
    intro n L g terms h hmap
    match n with
    | 0 => rw [dag0] at h; simp at h
    | 1 => rw [dag1] at h; simp at h
    | 2 => rw [dag2] at h; simp at h
    | 3 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, hg⟩ := hmap
        subst hL; subst hg
        simp [circuit, QuadCircuitData.layerAt, evalLayer, nodeSum, dag, wireMap, operandVal]
    | 4 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, hg⟩ := hmap
        subst hL; subst hg
        simp [circuit, QuadCircuitData.layerAt, evalLayer, nodeSum, dag, wireMap, operandVal]
    | (k + 5) => simp [wireMap] at hmap

/-- The circuit's single assertion record: node `3` (the product) is pinned to zero, carried
    by the materialized assertion wire `(0, 0)`. -/
def recs : List AssertionRec := [{ assertedNode := 3, wireLayer := 0, wireIndex := 0 }]

theorem backed (F : Type) [Field F] : ∀ r ∈ recs, Backed (circuit F) wireMap r := by
  intro r hr
  simp only [recs, List.mem_singleton] at hr
  subst hr
  left
  refine ⟨?_, 0, rfl, ?_⟩
  · show 0 < (circuit F).layers.length
    rw [nlayers_eq]; omega
  · show (⟨0, 0, 0, 0⟩ : QuadTerm F) ∈ ((circuit F).layerAt 0).terms
    rw [layer0]; simp

theorem covers (F : Type) [Field F] : CoversConstraints (circuit F) wireMap recs := by
  constructor
  · intro l hl t ht hk
    rw [nlayers_eq] at hl
    match l, hl with
    | 0, _ =>
        rw [layer0] at ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact ⟨rfl, ⟨{ assertedNode := 3, wireLayer := 0, wireIndex := 0 }, by simp [recs], rfl⟩⟩
    | 1, _ =>
        rw [layer1] at ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact absurd hk one_ne_zero
  · intro i hi
    rw [noutput_eq] at hi
    interval_cases i
    right
    intro t ht _
    rw [layer0] at ht
    simp only [List.mem_singleton] at ht
    subst ht
    rfl

/-- **Acceptance, in terms of the source-level assertion only.** No layers, no wires, no
    scheduling: the compiled circuit accepts exactly when the product of the two inputs is
    zero, which is what `assert0 (a * b)` says. -/
theorem accepts_iff_product_zero (F : Type) [Field F] (inputs : Nat → F) :
    Accepts (circuit F) inputs ↔ inputs 1 * inputs 2 = 0 := by
  rw [accepts_iff_assertions (circuit F) (dag F) wireMap inputs (valid F inputs) recs
    (backed F) (covers F) (by rw [nlayers_eq]; omega)]
  constructor
  · intro h
    have := h { assertedNode := 3, wireLayer := 0, wireIndex := 0 } (by simp [recs])
    simpa [interpDag, interpDagAux, dag, nodeValue, List.getD] using this
  · intro h r hr
    simp only [recs, List.mem_singleton] at hr
    subst hr
    simpa [interpDag, interpDagAux, dag, nodeValue, List.getD] using h

/-- **The payoff.** `simulation` turns the scheduling into a statement about the compiled
    circuit's wires: layer `1`, wire `0` carries the product of inputs `1` and `2`. Nothing
    about layers or scheduling appears on the right-hand side. -/
theorem wire_one_zero_is_product (F : Type) [Field F] (inputs : Nat → F) :
    wireValue (circuit F) inputs 1 0 = inputs 1 * inputs 2 := by
  have h := (simulation (circuit F) (dag F) wireMap inputs (valid F inputs) 3 1 0 rfl).2
    (by rw [nlayers_eq]; omega)
  rw [h]
  simp [interpDag, interpDagAux, dag, nodeValue, List.getD]

end Micro

end -- @[expose] public section
