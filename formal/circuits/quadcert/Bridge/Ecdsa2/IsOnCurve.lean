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
import ECDSA.EC

/-!
# Rung 0: a compiled circuit against its specification

The quad form of `EcCircuit::is_on_curve` (`rust/circuits/ec/src/circuit.rs:181`), transcribed
from the certificate sidecar of an actual `compile_with_cert` run, proved equivalent to
`AffinePoint.IsOnCurve` from `ECDSA/EC.lean`.

The compiled geometry, verbatim from the sidecar:

```
ninput=3  npublic_input=1  noutput=1  nlayers=2  nassertions=1
constants: c0 = 1, c1 = -b, c2 = -a (= 3 for P-256), c3 = -1
layer 0 (output): nw=4  (0,1,2,c3) (0,0,3,c0)
layer 1 (deepest): nw=3  (0,0,0,c0) (3,0,0,c1) (1,0,1,c0) (3,0,1,c2) (2,1,1,c0) (3,2,2,c0)
nodes: 0=Input0@(2,0) 1=Input1@(2,1) 2=Sum[(c0,1,1)]@(1,2) 3=Sum[(c0,0,1)]@(1,1)
       4=Input2@(2,2) 5=Sum[(c1,0,0),(c2,0,1),(c0,4,4)]@(1,3) 6=Sum[(c0,0,0)]@(1,0)
       7=Sum[(c3,2,3),(c0,5,6)]@(0,0) 8=Assert0(7)
assertion: asserted_node=7 wire=(0,0) paths=["is_on_curve"]
```

Input position `0` is the reserved constant `one` (`K_FIRST_WIRE_POSITION = 1`), position `1`
is `x`, position `2` is `y` — this is the *input layout*, and it is the one place where meaning
enters. The constants correspondence (`c1 = -b`, `c2 = -a`, `c3 = -1` against the dumped P-256
bytes) is likewise data, checked once; here `a` and `b` are carried symbolically so the proof
stays field-generic.
-/

namespace Rung0

open QuadCircuitData

variable {F : Type} [Field F]

/-- The compiled circuit, layer 0 = output. -/
def circuit (a b : F) : QuadCircuitData F where
  ninput := 3
  noutput := 1
  layers :=
    [ { ninput := 4, terms := [⟨0, 1, 2, -1⟩, ⟨0, 0, 3, 1⟩] },
      { ninput := 3,
        terms := [⟨0, 0, 0, 1⟩, ⟨3, 0, 0, -b⟩, ⟨1, 0, 1, 1⟩,
                  ⟨3, 0, 1, -a⟩, ⟨2, 1, 1, 1⟩, ⟨3, 2, 2, 1⟩] } ]

/-- The post-materialization quad DAG. -/
def dag (a b : F) : List (DagNode F) :=
  [ .input 0,
    .input 1,
    .sum [⟨1, 1, 1⟩],
    .sum [⟨1, 0, 1⟩],
    .input 2,
    .sum [⟨-b, 0, 0⟩, ⟨-a, 0, 1⟩, ⟨1, 4, 4⟩],
    .sum [⟨1, 0, 0⟩],
    .sum [⟨-1, 2, 3⟩, ⟨1, 5, 6⟩],
    .assert0 7 ]

/-- Node → wire, inputs at the pseudo-layer `nlayers = 2`. -/
def wireMap : WireMap
  | 0 => some (2, 0)
  | 1 => some (2, 1)
  | 2 => some (1, 2)
  | 3 => some (1, 1)
  | 4 => some (2, 2)
  | 5 => some (1, 3)
  | 6 => some (1, 0)
  | 7 => some (0, 0)
  | _ => none

/-- The single assertion record, path `is_on_curve`. A last-layer assertion: node 7 is the
    output wire itself, not a materialized assertion term. -/
def recs : List AssertionRec := [{ assertedNode := 7, wireLayer := 0, wireIndex := 0 }]

section Lookups
variable (a b : F)

private lemma nlayers_eq : (circuit a b).layers.length = 2 := rfl
private lemma noutput_eq : (circuit a b).noutput = 1 := rfl
private lemma layer0 : (circuit a b).layerAt 0 = LayerData.mk 4 [⟨0, 1, 2, -1⟩, ⟨0, 0, 3, 1⟩] := rfl
private lemma layer1 : (circuit a b).layerAt 1 = LayerData.mk 3 [⟨0, 0, 0, 1⟩, ⟨3, 0, 0, -b⟩, ⟨1, 0, 1, 1⟩, ⟨3, 0, 1, -a⟩, ⟨2, 1, 1, 1⟩, ⟨3, 2, 2, 1⟩] := rfl

private lemma dagN0 : (dag a b).getD 0 (.input 0) = .input 0 := rfl
private lemma dagN1 : (dag a b).getD 1 (.input 0) = .input 1 := rfl
private lemma dagN2 : (dag a b).getD 2 (.input 0) = .sum [⟨(1 : F), 1, 1⟩] := rfl
private lemma dagN3 : (dag a b).getD 3 (.input 0) = .sum [⟨(1 : F), 0, 1⟩] := rfl
private lemma dagN4 : (dag a b).getD 4 (.input 0) = .input 2 := rfl
private lemma dagN5 :
    (dag a b).getD 5 (.input 0) = .sum [⟨-b, 0, 0⟩, ⟨-a, 0, 1⟩, ⟨(1 : F), 4, 4⟩] := rfl
private lemma dagN6 : (dag a b).getD 6 (.input 0) = .sum [⟨(1 : F), 0, 0⟩] := rfl
private lemma dagN7 :
    (dag a b).getD 7 (.input 0) = .sum [⟨(-1 : F), 2, 3⟩, ⟨(1 : F), 5, 6⟩] := rfl
private lemma dagN8 : (dag a b).getD 8 (.input 0) = .assert0 7 := rfl
private lemma dagBig (k : Nat) : (dag a b).getD (k + 9) (.input 0) = .input 0 :=
  List.getD_eq_default _ _ (by simp only [dag, List.length_cons, List.length_nil]; omega)

end Lookups

/-- Left inverse of `wireMap` on the mapped nodes; makes injectivity a linear check. -/
private def wireInv : Nat × Nat → Nat
  | (2, 0) => 0
  | (2, 1) => 1
  | (1, 2) => 2
  | (1, 1) => 3
  | (2, 2) => 4
  | (1, 3) => 5
  | (1, 0) => 6
  | (0, 0) => 7
  | _ => 8

private lemma wireInv_wireMap {n : Nat} {p : Nat × Nat} (h : wireMap n = some p) :
    wireInv p = n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp only [wireMap, Option.some.injEq] at h; subst h; rfl
  | 8 => simp [wireMap] at h
  | (_ + 9) => simp [wireMap] at h

private lemma mapped_lt_nine {n : Nat} {p : Nat × Nat} (h : wireMap n = some p) : n < 9 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
  | (_ + 9) => simp [wireMap] at h

/-- **The scheduling is valid.** Every field is discharged against the transcribed sidecar. -/
theorem valid (a b : F) (inputs : Nat → F) :
    ValidScheduling (circuit a b) (dag a b) wireMap inputs where
  map_inrange := by
    intro n L g h
    have := mapped_lt_nine h
    simp only [dag, List.length_cons, List.length_nil]
    omega
  wire_inj := by
    intro m n L g hm hn
    rw [← wireInv_wireMap hm, ← wireInv_wireMap hn]
  input_wire := by
    intro n pos hn h
    match n with
    | 0 => rw [dagN0] at h; injection h with hp; subst hp; rfl
    | 1 => rw [dagN1] at h; injection h with hp; subst hp; rfl
    | 4 => rw [dagN4] at h; injection h with hp; subst hp; rfl
    | 2 => rw [dagN2] at h; simp at h
    | 3 => rw [dagN3] at h; simp at h
    | 5 => rw [dagN5] at h; simp at h
    | 6 => rw [dagN6] at h; simp at h
    | 7 => rw [dagN7] at h; simp at h
    | 8 => rw [dagN8] at h; simp at h
    | (k + 9) =>
        exfalso; simp only [dag, List.length_cons, List.length_nil] at hn; omega
  assert0_nowire := by
    intro n w h
    match n with
    | 0 => rw [dagN0] at h; simp at h
    | 1 => rw [dagN1] at h; simp at h
    | 2 => rw [dagN2] at h; simp at h
    | 3 => rw [dagN3] at h; simp at h
    | 4 => rw [dagN4] at h; simp at h
    | 5 => rw [dagN5] at h; simp at h
    | 6 => rw [dagN6] at h; simp at h
    | 7 => rw [dagN7] at h; simp at h
    | 8 => rfl
    | (k + 9) => rw [dagBig] at h; simp at h
  sum_inrange := by
    intro n L g terms h hmap
    match n with
    | 0 => rw [dagN0] at h; simp at h
    | 1 => rw [dagN1] at h; simp at h
    | 4 => rw [dagN4] at h; simp at h
    | 8 => rw [dagN8] at h; simp at h
    | 2 | 3 | 5 | 6 | 7 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        rw [nlayers_eq]; omega
    | (k + 9) => simp [wireMap] at hmap
  sum_operands := by
    intro n L g terms t h hmap ht
    match n with
    | 0 => rw [dagN0] at h; simp at h
    | 1 => rw [dagN1] at h; simp at h
    | 4 => rw [dagN4] at h; simp at h
    | 8 => rw [dagN8] at h; simp at h
    | 2 =>
        rw [dagN2] at h; injection h with ht2; subst ht2
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap; subst hL
        simp only [List.mem_singleton] at ht; subst ht
        exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
    | 3 =>
        rw [dagN3] at h; injection h with ht2; subst ht2
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap; subst hL
        simp only [List.mem_singleton] at ht; subst ht
        exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
    | 5 =>
        rw [dagN5] at h; injection h with ht2; subst ht2
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap; subst hL
        fin_cases ht <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    | 6 =>
        rw [dagN6] at h; injection h with ht2; subst ht2
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap; subst hL
        simp only [List.mem_singleton] at ht; subst ht
        exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
    | 7 =>
        rw [dagN7] at h; injection h with ht2; subst ht2
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, _⟩ := hmap; subst hL
        fin_cases ht <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    | (k + 9) => simp [wireMap] at hmap
  sum_operands_lt := by
    intro n terms h t ht
    match n with
    | 0 => rw [dagN0] at h; simp at h
    | 1 => rw [dagN1] at h; simp at h
    | 4 => rw [dagN4] at h; simp at h
    | 8 => rw [dagN8] at h; simp at h
    | 2 => rw [dagN2] at h; injection h with h2; subst h2; fin_cases ht <;> simp_all
    | 3 => rw [dagN3] at h; injection h with h2; subst h2; fin_cases ht <;> simp_all
    | 5 => rw [dagN5] at h; injection h with h2; subst h2; fin_cases ht <;> simp_all
    | 6 => rw [dagN6] at h; injection h with h2; subst h2; fin_cases ht <;> simp_all
    | 7 => rw [dagN7] at h; injection h with h2; subst h2; fin_cases ht <;> simp_all
    | (k + 9) => rw [dagBig] at h; simp at h
  sum_local := by
    intro n L g terms h hmap
    match n with
    | 0 => rw [dagN0] at h; simp at h
    | 1 => rw [dagN1] at h; simp at h
    | 4 => rw [dagN4] at h; simp at h
    | 8 => rw [dagN8] at h; simp at h
    | 2 | 3 | 5 | 6 | 7 =>
        simp only [wireMap, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hL, hg⟩ := hmap; subst hL; subst hg
        simp [circuit, QuadCircuitData.layerAt, evalLayer, nodeSum, dag, wireMap, operandVal,
              QuadCircuitData.inputValuation, wireValue, layerValuations, valuationsAux]
        try ring
    | (k + 9) => simp [wireMap] at hmap

theorem backed (a b : F) : ∀ r ∈ recs, Backed (circuit a b) wireMap r := by
  intro r hr
  simp only [recs, List.mem_singleton] at hr
  subst hr
  right
  exact ⟨by show (0 : Nat) < (circuit a b).noutput; rw [noutput_eq]; omega, rfl⟩

/-- Coverage needs the curve constants to be non-zero: a zero constant in a `Sum` term would be
    read by the runtime as an *assertion* term (`eval.rs:139`), silently adding a constraint.
    The compiler forbids it (`scheduler.rs::assert_layering` rejects `k = 0` in a sum), and for
    P-256 `a = -3`, `b ≠ 0`; here it is an explicit hypothesis. -/
theorem covers (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    CoversConstraints (circuit a b) wireMap recs := by
  constructor
  · intro l hl t ht hk
    rw [nlayers_eq] at hl
    match l, hl with
    | 0, _ =>
        rw [layer0] at ht
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp at hk
    | 1, _ =>
        rw [layer1] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [] at hk <;>
          first
            | exact absurd hk one_ne_zero
            | (exact absurd (neg_eq_zero.mp hk) hb)
            | (exact absurd (neg_eq_zero.mp hk) ha)
  · intro i hi
    rw [noutput_eq] at hi
    interval_cases i
    left
    exact ⟨{ assertedNode := 7, wireLayer := 0, wireIndex := 0 }, by simp [recs], rfl⟩

/-- The asserted node's value, as an expression in the named inputs. This is the
    per-assertion "scripted induction" step of the plan's Phase 3, here for the single
    assertion `is_on_curve`. -/
private lemma interp7 (a b : F) (inputs : Nat → F) (hone : inputs 0 = 1) :
    interpDag (dag a b) inputs 7
      = inputs 2 * inputs 2 - (inputs 1 * inputs 1 * inputs 1 + a * inputs 1 + b) := by
  show (interpDagAux inputs (dag a b) []).getD 7 0 = _
  simp only [dag, interpDagAux, nodeValue, List.foldl_cons, List.foldl_nil,
    List.nil_append, List.cons_append, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hone]
  ring

/-- **Rung 0.** The compiled quad circuit accepts exactly the points on the curve.

    `hone` pins input position `0` to the constant `1` — the reserved wire
    (`K_FIRST_WIRE_POSITION = 1`) — and positions `1`, `2` carry `x` and `y`. That assignment is
    the input layout, and it is the only place where the theorem's meaning is chosen rather than
    checked. -/
theorem accepts_iff_isOnCurve (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (inputs : Nat → F) (hone : inputs 0 = 1)
    (params : CurveParameters F) (hpa : params.a = a) (hpb : params.b = b) :
    Accepts (circuit a b) inputs
      ↔ AffinePoint.IsOnCurve ⟨inputs 1, inputs 2⟩ params := by
  rw [accepts_iff_assertions (circuit a b) (dag a b) wireMap inputs (valid a b inputs) recs
    (backed a b) (covers a b ha hb) (by rw [nlayers_eq]; omega)]
  simp only [AffinePoint.IsOnCurve, hpa, hpb]
  constructor
  · intro h
    have h7 := h { assertedNode := 7, wireLayer := 0, wireIndex := 0 } (by simp [recs])
    rw [interp7 a b inputs hone] at h7
    linear_combination h7
  · intro h r hr
    simp only [recs, List.mem_singleton] at hr
    subst hr
    rw [interp7 a b inputs hone]
    linear_combination h

end Rung0
