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

import quadcert.Core.Check
import quadcert.Gen.Rung1.Rung1OkCheck
import quadcert.Gen.Rung1.Rung1InvCheck
import ECDSA.EC

/-!
# Rung 1, against generated data

`point_equality` + `is_on_curve` (`rust/circuits/ec/src/circuit.rs:162,181`), with the circuit,
DAG, wire map and assertion records **emitted by the dumper** (`cert::emit_lean`) rather than
transcribed. Nothing below is hand-written data; the only hand-written parts are the constants
correspondence, `sum_local`, and the meaning lemmas.

Seven of the eight `ValidScheduling` fields come from `validScheduling_of_checks` applied to the
generated `ok_check` / `inv_check` / `wireFn_lt`.
-/

namespace Rung1

open Quadcert Quadcert.Gen.Rung1

variable {F : Type} [Field F]

/-! ### Constants correspondence

The proofs below use the **generated** constant table (`Rung1Base.constNat`, canonical hex
integers from the artifact's own encoding), not a hand-written list read out of a comment.
`consts_spec` proves its correspondence to `CurveParameters`: `c0 = 1`, `c2 = -a` and `c4 = 0`
hold outright, while `c1 = -b` and `c3 = -1` need the characteristic, because the artifact
encodes them as `p - b` and `p - 1`.

This is where the P-256 choice enters the proof, and it now enters as an explicit hypothesis
rather than as prose. -/

/-- The table the proofs below use. -/
def constsOf (a b : F) : Nat → F := fun i => [1, -b, -a, -1, 0].getD i 0

/-- The **generated** table: canonical integers from the artifact's own encoding, cast into
    the field. The generated modules are Mathlib-free, so this one line lives on the spec
    side. -/
def consts (F : Type) [Field F] : Nat → F := fun i => (constNat i : F)

/-- The constant table obtained directly from the verified LFC3 decoder. -/
def artifactConsts (F : Type) [Field F] : Nat → F :=
  fun i => (Quadcert.Gen.Rung1Artifact.decoded.constNat i : F)

theorem consts_eq_artifact (F : Type) [Field F] : consts F = artifactConsts F := by
  funext i
  simp only [consts, artifactConsts]
  rw [← congrFun constNat_from_artifact i]

/-- P-256's base field modulus. -/
abbrev p256 : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- P-256's curve constant `b`, as the canonical integer the artifact encodes. -/
abbrev bNat : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

theorem consts_0 (F : Type) [Field F] : consts F 0 = 1 := by simp [consts, constNat]
theorem consts_4 (F : Type) [Field F] : consts F 4 = 0 := by simp [consts, constNat]

theorem consts_2 (F : Type) [Field F] (a : F) (ha : a = -3) : consts F 2 = -a := by
  rw [ha]; show ((constNat 2 : Nat) : F) = _; simp [constNat]; try ring

theorem consts_3 (F : Type) [Field F] [CharP F p256] : consts F 3 = -1 := by
  show ((constNat 3 : Nat) : F) = -1
  rw [show (constNat 3) = p256 - 1 from rfl, cast_sub_eq_neg p256 1 (by norm_num)]
  simp

theorem consts_1 (F : Type) [Field F] [CharP F p256] (b : F) (hb : b = (bNat : F)) :
    consts F 1 = -b := by
  show ((constNat 1 : Nat) : F) = -b
  rw [hb, show (constNat 1) = p256 - bNat from rfl, cast_sub_eq_neg p256 bNat (by norm_num)]

/-- **The constants correspondence, as a theorem.** The table the proofs use is exactly the
    generated one — canonical integers read out of the artifact's own encoding — under the
    P-256 characteristic and the curve parameters. This replaces a human reading `c1 = -b`
    out of a comment in the generated header. -/
theorem constsOf_eq_generated (F : Type) [Field F] [CharP F p256] (a b : F)
    (ha : a = -3) (hb : b = (bNat : F)) : constsOf a b = consts F := by
  funext i
  match i with
  | 0 => rw [consts_0]; rfl
  | 1 => rw [consts_1 F b hb]; rfl
  | 2 => rw [consts_2 F a ha]; rfl
  | 3 => rw [consts_3]; rfl
  | 4 => rw [consts_4]; rfl
  | (_ + 5) => simp [constsOf, consts, constNat]

@[reducible] noncomputable def circuit (a b : F) : QuadCircuitData F := raw.toQuad (constsOf a b)
@[reducible] noncomputable def dagOf (a b : F) : List (DagNode F) := raw.toDag (constsOf a b)
@[reducible] noncomputable def recsOf : List AssertionRec := raw.toRecs

private lemma nlayers_eq (a b : F) : (circuit a b).layers.length = 2 := rfl
private lemma noutput_eq (a b : F) : (circuit a b).noutput = 4 := rfl

/-- The one non-structural `ValidScheduling` field. Each of the 11 sum nodes is checked by
    unfolding both sides and normalising; the `ring` is needed because `canonical_term` sorts
    `(h0, h1)`, so the layer term and the DAG term differ by commutativity. -/
theorem sum_local_holds (a b : F) (inputs : Nat → F) :
    ∀ n L g terms,
      (dagOf a b).getD n (.input 0) = .sum terms → raw.toWireMap n = some (L, g) →
      evalLayer ((circuit a b).layerAt L) ((circuit a b).inputValuation inputs L) g =
        nodeSum (dagOf a b) raw.toWireMap ((circuit a b).inputValuation inputs L) (L + 1) n := by
  intro n L g terms h hmap
  match n with
  | 0 | 1 | 3 | 8 | 13 | 16 | 12 => simp [dagOf, raw, nodes_0, RawCircuit.toDag] at h
  | 2 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 14 | 15 | 17 | 18 =>
      simp only [raw, RawCircuit.toWireMap, wireFn, wireFn_0] at hmap
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmap)
      simp [circuit, dagOf, raw, nodes_0, constsOf, RawCircuit.toQuad, RawCircuit.toDag,
        RawLayer.toLayer, rawTerm, RawCircuit.toWireMap, wireFn, wireFn_0, QuadCircuitData.layerAt, evalLayer,
        nodeSum, operandVal, QuadCircuitData.inputValuation, wireValue, layerValuations,
        valuationsAux]
      try ring
  | (_ + 19) => simp [raw, RawCircuit.toWireMap, wireFn, wireFn_0] at hmap

/-- **The scheduling is valid** — seven fields generic, one supplied. -/
theorem valid (a b : F) (inputs : Nat → F) :
    ValidScheduling (circuit a b) (dagOf a b) raw.toWireMap inputs :=
  validScheduling_of_checks raw (constsOf a b) inputs wireInv ok_check inv_check wireFn_lt
    (sum_local_holds a b inputs)

/-! ### Lookups against the generated data -/

section Lookups
variable (a b : F)
private lemma layer0 : (circuit a b).layerAt 0 =
    LayerData.mk 7 [⟨0, 1, 2, -1⟩, ⟨0, 0, 3, 1⟩, ⟨1, 4, 4, 0⟩, ⟨2, 5, 5, 0⟩, ⟨3, 6, 6, 0⟩] := rfl
private lemma layer1 : (circuit a b).layerAt 1 =
    LayerData.mk 7 [⟨0, 0, 0, 1⟩, ⟨3, 0, 0, -b⟩, ⟨6, 0, 0, -1⟩, ⟨1, 0, 1, 1⟩, ⟨3, 0, 1, -a⟩,
      ⟨4, 0, 1, -1⟩, ⟨2, 1, 1, 1⟩, ⟨5, 0, 2, -1⟩, ⟨3, 2, 2, 1⟩, ⟨4, 3, 6, 1⟩, ⟨5, 4, 6, 1⟩,
      ⟨6, 5, 6, 1⟩] := rfl
private lemma recs_eq : (recsOf : List AssertionRec) =
    [⟨11, 0, 0⟩, ⟨4, 0, 1⟩, ⟨14, 0, 2⟩, ⟨17, 0, 3⟩] := rfl
end Lookups

/-! ### Input layout

`Layout` is generated from the sidecar's layout table (`LayoutBuilder`); these are the only
names by which the theorem below refers to inputs. -/

/-! ### The assertion bridge -/

theorem backed (a b : F) : ∀ r ∈ recsOf, Backed (circuit a b) raw.toWireMap r := by
  intro r hr
  rw [recs_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · right
    exact ⟨by show (0 : Nat) < (circuit a b).noutput; rw [noutput_eq]; omega, rfl⟩
  · left
    refine ⟨by show (0 : Nat) < (circuit a b).layers.length; rw [nlayers_eq]; omega, 4, rfl, ?_⟩
    show (⟨1, 4, 4, 0⟩ : QuadTerm F) ∈ ((circuit a b).layerAt 0).terms
    rw [layer0]; simp
  · left
    refine ⟨by show (0 : Nat) < (circuit a b).layers.length; rw [nlayers_eq]; omega, 5, rfl, ?_⟩
    show (⟨2, 5, 5, 0⟩ : QuadTerm F) ∈ ((circuit a b).layerAt 0).terms
    rw [layer0]; simp
  · left
    refine ⟨by show (0 : Nat) < (circuit a b).layers.length; rw [nlayers_eq]; omega, 6, rfl, ?_⟩
    show (⟨3, 6, 6, 0⟩ : QuadTerm F) ∈ ((circuit a b).layerAt 0).terms
    rw [layer0]; simp

/-- Coverage. The three `point_equality` assertions are materialized `k = 0` terms; their
    output wires carry no information and are discharged by `structurallyZero`. The curve
    constants must be non-zero, else a `Sum` term would be read as an assertion term. -/
theorem covers (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    CoversConstraints (circuit a b) raw.toWireMap recsOf := by
  rw [recs_eq]
  constructor
  · intro l hl t ht hk
    rw [nlayers_eq] at hl
    match l, hl with
    | 0, _ =>
        rw [layer0] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact absurd hk (by simp)
        · exact absurd hk one_ne_zero
        · exact ⟨rfl, ⟨⟨4, 0, 1⟩, by simp, rfl⟩⟩
        · exact ⟨rfl, ⟨⟨14, 0, 2⟩, by simp, rfl⟩⟩
        · exact ⟨rfl, ⟨⟨17, 0, 3⟩, by simp, rfl⟩⟩
    | 1, _ =>
        exfalso
        rw [layer1] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          first
            | exact one_ne_zero hk
            | exact (by simp : (-1 : F) ≠ 0) hk
            | exact hb (neg_eq_zero.mp hk)
            | exact ha (neg_eq_zero.mp hk)
  · intro i hi
    rw [noutput_eq] at hi
    interval_cases i
    · left; exact ⟨⟨11, 0, 0⟩, by simp, rfl⟩
    all_goals
      right
      intro t ht hg
      rw [layer0] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl <;> simp_all

/-! ### Per-assertion meaning lemmas

One per named path. This is the only place where meaning enters. -/

/-- **A template schema.** Rung 1's `px_eq`, `py_eq` and `z_zinv` are three instances of one
    template — `sum [(-1, u, v), (1, w, x)]`. The unfolding and `ring` happen **once**, with
    the leaf nodes as parameters; each instance supplies its own leaves.

    This is the mechanism Phase B needs at ECDSA2 scale, where 52 templates cover 1,048
    assertions. Note the leaves are arbitrary node indices, not an arithmetic family: measured,
    the 256 instances of `slice_wx` have irregular node indices, irregular input positions and
    non-uniform leaf counts, so an indexed family `∀ i < 256, …` is not statable. Parameterising
    by leaves sidesteps that entirely. -/
theorem diffTemplate (a b : F) (inputs : Nat → F) (n u v w x : Nat)
    (hn : (dagOf a b).getD n (.input 0) = .sum [⟨-1, u, v⟩, ⟨1, w, x⟩])
    (hu : u < n) (hv : v < n) (hw : w < n) (hx : x < n) :
    interpDag (dagOf a b) inputs n
      = interpDag (dagOf a b) inputs w * interpDag (dagOf a b) inputs x
        - interpDag (dagOf a b) inputs u * interpDag (dagOf a b) inputs v := by
  rw [interpDag_sum inputs (dagOf a b) n _ hn (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact ⟨by assumption, by assumption⟩)]
  simp only [List.foldl_cons, List.foldl_nil]
  ring

/-- Leaves of the Rung 1 DAG, by input position. -/
private lemma leaf (a b : F) (inputs : Nat → F) (n pos : Nat) (hn : n < 19)
    (h : (dagOf a b).getD n (.input 0) = .input pos) :
    interpDag (dagOf a b) inputs n = inputs pos :=
  interpDag_input _ _ n pos (by simp [dagOf, raw, nodes_0, RawCircuit.toDag]; omega) h

private lemma interpVals (a b : F) (inputs : Nat → F) (hone : inputs Layout.one = 1) :
    interpDag (dagOf a b) inputs 4
        = inputs Layout.zinv * inputs Layout.qx - inputs Layout.px
      ∧ interpDag (dagOf a b) inputs 14
        = inputs Layout.zinv * inputs Layout.qy - inputs Layout.py
      ∧ interpDag (dagOf a b) inputs 17
        = inputs Layout.zinv * inputs Layout.qz - 1
      ∧ interpDag (dagOf a b) inputs 11
        = inputs Layout.py * inputs Layout.py
            - (inputs Layout.px * inputs Layout.px * inputs Layout.px
               + a * inputs Layout.px + b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- three instances of one template: schema application plus each instance's own leaves
  · rw [diffTemplate a b inputs 4 0 1 2 3 rfl (by omega) (by omega) (by omega) (by omega),
      leaf a b inputs 0 Layout.one (by omega) rfl, leaf a b inputs 1 Layout.px (by omega) rfl,
      leaf a b inputs 2 Layout.zinv (by omega) rfl, leaf a b inputs 3 Layout.qx (by omega) rfl,
      hone]
    ring
  · rw [diffTemplate a b inputs 14 0 8 2 13 rfl (by omega) (by omega) (by omega) (by omega),
      leaf a b inputs 0 Layout.one (by omega) rfl, leaf a b inputs 8 Layout.py (by omega) rfl,
      leaf a b inputs 2 Layout.zinv (by omega) rfl, leaf a b inputs 13 Layout.qy (by omega) rfl,
      hone]
    ring
  · rw [diffTemplate a b inputs 17 0 0 2 16 rfl (by omega) (by omega) (by omega) (by omega),
      leaf a b inputs 0 Layout.one (by omega) rfl, leaf a b inputs 2 Layout.zinv (by omega) rfl,
      leaf a b inputs 16 Layout.qz (by omega) rfl, hone]
    ring
  · simp only [interpDag, dagOf, raw, nodes_0, constsOf, RawCircuit.toDag, interpDagAux, nodeValue,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Layout.one, hone]
    ring

/-- **Rung 1.** The compiled circuit accepts exactly when `zinv` inverts `qz`, the projective
    point `(qx : qy : qz)` represents the affine point `(px, py)`, and that point is on the
    curve. Everything on the left is generated from the circuit bytes; everything on the right
    is `ECDSA/EC.lean` vocabulary. -/
theorem accepts_iff_spec (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (inputs : Nat → F) (hone : inputs Layout.one = 1)
    (params : CurveParameters F) (hpa : params.a = a) (hpb : params.b = b) :
    Accepts (circuit a b) inputs
      ↔ (inputs Layout.qz * inputs Layout.zinv = 1
          ∧ ProjectiveEquiv
              ⟨inputs Layout.qx, inputs Layout.qy, inputs Layout.qz⟩
              (AffinePoint.mk (inputs Layout.px) (inputs Layout.py)).toProjective
          ∧ AffinePoint.IsOnCurve ⟨inputs Layout.px, inputs Layout.py⟩ params) := by
  obtain ⟨e4, e14, e17, e11⟩ := interpVals a b inputs hone
  rw [accepts_iff_assertions (circuit a b) (dagOf a b) raw.toWireMap inputs (valid a b inputs)
      recsOf (backed a b) (covers a b ha hb) (by rw [nlayers_eq]; omega),
    projectiveEquiv_toProjective_iff]
  simp only [AffinePoint.IsOnCurve, hpa, hpb]
  rw [recs_eq]
  constructor
  · intro h
    have h4 := h ⟨4, 0, 1⟩ (by simp)
    have h14 := h ⟨14, 0, 2⟩ (by simp)
    have h17 := h ⟨17, 0, 3⟩ (by simp)
    have h11 := h ⟨11, 0, 0⟩ (by simp)
    rw [e4] at h4; rw [e14] at h14; rw [e17] at h17; rw [e11] at h11
    have hz : inputs Layout.qz * inputs Layout.zinv = 1 := by linear_combination h17
    have hzne : inputs Layout.qz ≠ 0 := by
      intro hc; rw [hc, zero_mul] at hz; exact zero_ne_one hz
    refine ⟨hz, ⟨?_, ?_, hzne⟩, by linear_combination h11⟩
    · linear_combination inputs Layout.qz * h4 - inputs Layout.qx * hz
    · linear_combination inputs Layout.qz * h14 - inputs Layout.qy * hz
  · rintro ⟨hz, ⟨hx, hy, _⟩, hoc⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [e11]; linear_combination hoc
    · rw [e4]; linear_combination inputs Layout.zinv * hx + inputs Layout.px * hz
    · rw [e14]; linear_combination inputs Layout.zinv * hy + inputs Layout.py * hz
    · rw [e17]; linear_combination hz

/-! ### Committed-byte entry point -/

/-- The circuit interpreted from the packed, committed LFC3 bytes, including its decoded
    constants.  `artifactRaw_eq_raw` makes the generated literal used above a checked cache. -/
@[reducible] noncomputable def artifactCircuit (F : Type) [Field F] : QuadCircuitData F :=
  artifactRaw.toQuad (artifactConsts F)

/-- End-to-end bridge: the circuit decoded from packed LFC3 bytes satisfies the same
    handwritten specification.  The SHA root for those exact packed bytes is
    `Rung1Artifact.formalRoot`, proved in `Rung1ArtifactCommitment`. -/
theorem accepts_artifact_iff_spec [CharP F p256]
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (haCanonical : a = -3) (hbCanonical : b = (bNat : F))
    (inputs : Nat → F) (hone : inputs Layout.one = 1)
    (params : CurveParameters F) (hpa : params.a = a) (hpb : params.b = b) :
    Accepts (artifactCircuit F) inputs
      ↔ (inputs Layout.qz * inputs Layout.zinv = 1
          ∧ ProjectiveEquiv
              ⟨inputs Layout.qx, inputs Layout.qy, inputs Layout.qz⟩
              (AffinePoint.mk (inputs Layout.px) (inputs Layout.py)).toProjective
          ∧ AffinePoint.IsOnCurve ⟨inputs Layout.px, inputs Layout.py⟩ params) := by
  have hconstants : constsOf a b = artifactConsts F :=
    (constsOf_eq_generated F a b haCanonical hbCanonical).trans (consts_eq_artifact F)
  rw [artifactCircuit, artifactRaw_eq_raw, ← hconstants]
  exact accepts_iff_spec a b ha hb inputs hone params hpa hpb

end Rung1
