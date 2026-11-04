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
public import ECDSA.EC
public import ECDSA.ECBridge

/-
This Lean 4 formalization structurally models and verifies the `assert_public_key` logic defined in
`google3/privacy/proofs/zk/lib/circuits/tests/ec/pk_circuit.h`.

It imports curve definitions, projective arithmetic, and curve-preservation lemmas from
`ECDSA.EC` and `ECDSA.ECBridge`.

Outline of the file:
- `pureLoopResult` / `scalarMulProjective` : Mathematical specification of the loop.
- `Witness` : Structure for ZK witness lists (bits and intermediate coordinates).
- `IsCircuitBitMuxValid` : Models the conditional multiplexing of base points.
- `AssertEqualProjective` : Models the C++ `assert_equal_projective` cross-multiplication constraints.
- `LoopConstraints` / `loopResult` : Models the original C++ loop constraints and accumulator updates.
- `ValidPublicKeyWitness` : Bundles the exact constraints enforced by `assert_public_key`.
- `scalarMulProjective_equiv_bsmul` : Bridges `scalarMulProjective` to `bsmul`.
- `assert_public_key_sound` : Soundness theorem deriving curve membership and projective equivalence to `bsmul`.
- `LoopConstraintsZipped` / `loopResultZipped` / `ValidPublicKeyWitnessZipped` : Alternative zipped formulation.
- `assert_public_key_sound_zipped` : Soundness theorem for the zipped formulation.
-/

@[expose] public section

/-!
### Mathematical Specification
Formal definitions mapping cryptographic algebraic structure over elliptic curves
-/

section MathSpec

/--
  Precisely models native cryptographic scalar multiplication double-and-add logic mathematically.
-/
def pureLoopResult {F : Type} [Field F] : ProjectivePoint F → List Bool → CurveParameters F → ProjectivePoint F
| acc, [] => fun _ => acc
| acc, b :: bs => fun params =>
    let tx := if b then params.gx else 0
    let ty := if b then params.gy else 1
    let tz := if b then 1 else 0
    let nextAcc := circuitStep acc b tx ty tz params
    pureLoopResult nextAcc bs params

/--
  Redefines cryptographic scalar multiplication strictly as pure mathematical projective accumulation.
-/
noncomputable def scalarMulProjective {F : Type} [Field F] (s : List Bool) (params : CurveParameters F) : ProjectivePoint F :=
  pureLoopResult infinityPoint s params

end MathSpec

/-!
### ZK Circuit Logic & State Machine
The methods in this section model the C++ code that defines a circuit.
-/
section CircuitLogic
/--
  Represents the witness lists provided to the circuit, containing the scalar bits
  and the intermediate state coordinates for step-by-step verification.
-/
structure Witness (F : Type) where
  bits : List Bool
  int_x : List F
  int_y : List F
  int_z : List F

/--
  Models the conditional multiplexing logic inside the `assert_public_key` main loop
  of `circuits/tests/ec/pk_circuit.h`.
  Specifically, it captures the three `lc_.mux` operations that conditionally select
  between the base curve generator `G = (gx, gy, 1)` and the point at infinity `(0, 1, 0)`
  based on the current scalar bit `b`.
-/
def IsCircuitBitMuxValid {F : Type} [Field F] (b : Bool) (tx ty tz : F) (params : CurveParameters F) : Prop :=
  if b then
    tx = params.gx ∧ ty = params.gy ∧ tz = 1
  else
    tx = 0 ∧ ty = 1 ∧ tz = 0

/--
  Models `assert_equal_projective` in `circuits/tests/ec/pk_circuit.h`:
  checks the cross-multiplications `X1 * Z2 = X2 * Z1` and `Y1 * Z2 = Y2 * Z1`.
-/
def AssertEqualProjective {F : Type} [CommRing F] (p1 p2 : ProjectivePoint F) : Prop :=
  p1.X * p2.Z = p2.X * p1.Z ∧ p1.Y * p2.Z = p2.Y * p1.Z

/--
  Models the constraint bindings inside the main `for` loop of `assert_public_key` in
  `circuits/tests/ec/pk_circuit.h`.
  Specifically, it captures the `lc_.assert_eq` calls that enforce the step evaluation
  matches the externally provided intermediate witness arrays `int_x`, `int_y`, and `int_z`.
-/
def LoopConstraints {F : Type} [Field F] :
  ProjectivePoint F → List Bool → List F → List F → List F → CurveParameters F → Prop
| _, [], _, _, _, _ => True
| _, [_], [], [], [], _ => True
| acc, b :: bs@(_::_), wx :: wxs, wy :: wys, wz :: wzs, params =>
  ∃ (tx ty tz : F),
    IsCircuitBitMuxValid b tx ty tz params ∧
    let nextAcc := circuitStep acc b tx ty tz params
    nextAcc.X = wx ∧ nextAcc.Y = wy ∧ nextAcc.Z = wz ∧
    LoopConstraints { X := wx, Y := wy, Z := wz } bs wxs wys wzs params
| _, _, _, _, _, _ => False

/--
  Models the computational state transformation inside the main `for` loop of
  `assert_public_key` in `circuits/tests/ec/pk_circuit.h`.
  It tracks the accumulator re-assignments (`ax = w.int_x[i];` etc.) step-by-step
  to derive the exact final `ProjectivePoint` state upon exiting the loop.
-/
def loopResult {F : Type} [Field F] :
  ProjectivePoint F → List Bool → List F → List F → List F → CurveParameters F → ProjectivePoint F
| acc, [], _, _, _, _ => acc
| acc, [b], [], [], [], params =>
    let tx := if b then params.gx else 0
    let ty := if b then params.gy else 1
    let tz := if b then 1 else 0
    circuitStep acc b tx ty tz params
| _, _ :: bs@(_::_), wx :: wxs, wy :: wys, wz :: wzs, params =>
    loopResult { X := wx, Y := wy, Z := wz } bs wxs wys wzs params
| _, _, _, _, _, _ => infinityPoint

/--
  Models the entirety of the `assert_public_key` boundary function in
  `circuits/tests/ec/pk_circuit.h`: the unrolled loop constraints (`LoopConstraints`),
  the cross-multiplication check `assert_equal_projective(ax, ay, az, pk_x, pk_y, 1)`,
  and the affine curve validation check `is_on_curve(pk_x, pk_y)`.
-/
def ValidPublicKeyWitness {F : Type} [Field F] (w : Witness F) (pk : AffinePoint F) (params : CurveParameters F) : Prop :=
  w.bits.length = params.kBits ∧
  w.int_x.length = params.kBits - 1 ∧
  w.int_y.length = params.kBits - 1 ∧
  w.int_z.length = params.kBits - 1 ∧
  let acc0 := infinityPoint
  LoopConstraints acc0 w.bits w.int_x w.int_y w.int_z params ∧
  let finalAcc := loopResult acc0 w.bits w.int_x w.int_y w.int_z params
  AssertEqualProjective finalAcc pk.toProjective ∧
  pk.IsOnCurve params

def zipLists {F : Type} : List Bool → List F → List F → List F → List (Bool × ProjectivePoint F)
| [], _, _, _ => []
| [_], _, _, _ => []
| b :: bs@(_::_), x :: xs, y :: ys, z :: zs => (b, { X := x, Y := y, Z := z }) :: zipLists bs xs ys zs
| _, _, _, _ => []

def getLastBool (l : List Bool) : Bool :=
  match l with
  | [] => false
  | [b] => b
  | _ :: tail => getLastBool tail

def LoopConstraintsZipped {F : Type} [Field F] (acc : ProjectivePoint F) (zipped : List (Bool × ProjectivePoint F)) (params : CurveParameters F) : Prop :=
  match zipped with
  | [] => True
  | (b, w) :: tail =>
    (∃ (tx ty tz : F), IsCircuitBitMuxValid b tx ty tz params ∧ circuitStep acc b tx ty tz params = w) ∧
    LoopConstraintsZipped w tail params

def loopResultZipped {F : Type} [Field F] (acc : ProjectivePoint F) (zipped : List (Bool × ProjectivePoint F)) (last_b : Bool) (params : CurveParameters F) : ProjectivePoint F :=
  match zipped with
  | [] =>
    let tx := if last_b then params.gx else 0
    let ty := if last_b then params.gy else 1
    let tz := if last_b then 1 else 0
    circuitStep acc last_b tx ty tz params
  | (_, w) :: tail =>
    loopResultZipped w tail last_b params

def ValidPublicKeyWitnessZipped {F : Type} [Field F] (w : Witness F) (pk : AffinePoint F) (params : CurveParameters F) : Prop :=
  w.bits.length = params.kBits ∧
  w.int_x.length = params.kBits - 1 ∧
  w.int_y.length = params.kBits - 1 ∧
  w.int_z.length = params.kBits - 1 ∧
  let acc0 := infinityPoint
  let zipped := zipLists w.bits w.int_x w.int_y w.int_z
  LoopConstraintsZipped acc0 zipped params ∧
  let last_b := getLastBool w.bits
  let finalAcc := loopResultZipped acc0 zipped last_b params
  AssertEqualProjective finalAcc pk.toProjective ∧
  pk.IsOnCurve params

end CircuitLogic

/-!
### Verification & Soundness Proofs
Proves that the circuit logic corresponds to projective scalar multiplication (`bsmul`)
and derives `finalAcc.IsOnCurve` and `ProjectiveEquiv` from the circuit's polynomial constraints.
-/
section Verification

theorem isCircuitBitMuxValid_eq {F : Type} [Field F] (b : Bool) (tx ty tz : F) (params : CurveParameters F)
    (h : IsCircuitBitMuxValid b tx ty tz params) :
    tx = (if b then params.gx else 0) ∧ ty = (if b then params.gy else 1) ∧ tz = (if b then 1 else 0) := by
  unfold IsCircuitBitMuxValid at h
  cases b
  case false => exact h
  case true => exact h

theorem loopResult_eq_pureLoopResult {F : Type} [Field F] (acc : ProjectivePoint F) (bits : List Bool)
    (wX wY wZ : List F) (params : CurveParameters F)
    (h : LoopConstraints acc bits wX wY wZ params) :
    loopResult acc bits wX wY wZ params = pureLoopResult acc bits params := by
  induction bits generalizing acc wX wY wZ with
  | nil => cases wX <;> cases wY <;> cases wZ <;> rfl
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases wX
      · cases wY
        · cases wZ
          · rfl
          · exact False.elim h
        · exact False.elim h
      · exact False.elim h
    | cons b_next bs_tail =>
      cases wX
      · exact False.elim h
      · case cons wx wxs =>
        cases wY
        · exact False.elim h
        · case cons wy wys =>
          cases wZ
          · exact False.elim h
          case cons wz wzs =>
            rcases h with ⟨tx, ty, tz, h_mux, hacc_x, hacc_y, hacc_z, h_tail⟩
            have ⟨h_tx, h_ty, h_tz⟩ := isCircuitBitMuxValid_eq b tx ty tz params h_mux
            have ih_app := ih { X := wx, Y := wy, Z := wz } wxs wys wzs h_tail
            change loopResult { X := wx, Y := wy, Z := wz } (b_next :: bs_tail) wxs wys wzs params = pureLoopResult (circuitStep acc b (if b then params.gx else 0) (if b then params.gy else 1) (if b then 1 else 0) params) (b_next :: bs_tail) params
            rw [ih_app]
            have h_nextAcc_eq : circuitStep acc b (if b = true then params.gx else 0) (if b = true then params.gy else 1) (if b = true then 1 else 0) params = { X := wx, Y := wy, Z := wz } := by
              rw [←h_tx, ←h_ty, ←h_tz]
              apply ProjectivePoint.ext
              · exact hacc_x
              · exact hacc_y
              · exact hacc_z
            rw [h_nextAcc_eq]

lemma pureLoopResult_append {F : Type} [Field F]
    (acc : ProjectivePoint F) (s1 s2 : List Bool) (params : CurveParameters F) :
    pureLoopResult acc (s1 ++ s2) params = pureLoopResult (pureLoopResult acc s1 params) s2 params := by
  induction s1 generalizing acc with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- Inductive curve-membership invariant noted in `pk_circuit.h`: starting on the curve, every step stays on the curve. -/
lemma pureLoopResult_on_curve {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
    (acc : ProjectivePoint F) (bits : List Bool) (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_acc : acc.IsOnCurve params)
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params) :
    (pureLoopResult acc bits params).IsOnCurve params := by
  induction bits generalizing acc with
  | nil => exact h_acc
  | cons b bs ih =>
    dsimp [pureLoopResult]
    apply ih
    unfold circuitStep
    have h_dbl : (doubleE acc params).IsOnCurve params := doubleE_on_curve acc params h_acc
    have h_mux : ({ X := if b then params.gx else 0, Y := if b then params.gy else 1, Z := if b then 1 else 0 } : ProjectivePoint F).IsOnCurve params := by
      cases b
      · exact infinity_on_curve params
      · exact affine_to_projective_on_curve { X := params.gx, Y := params.gy } params h_G
    exact addE_on_curve _ _ params h_dbl h_mux

/-- Proves that `assert_equal_projective(ax, ay, az, pk_x, pk_y, 1)` implies `ProjectiveEquiv` whenever `(ax, ay, az)` is on the curve. -/
lemma projectiveEquiv_of_assertEqualProjective {F : Type} [Field F]
    (p : ProjectivePoint F) (pk : AffinePoint F) (params : CurveParameters F)
    (hp : p.IsOnCurve params)
    (heq : AssertEqualProjective p pk.toProjective) :
    ProjectiveEquiv p pk.toProjective := by
  rcases heq with ⟨hx, hy⟩
  dsimp [AffinePoint.toProjective] at hx hy
  rw [mul_one] at hx hy
  have hz_ne : p.Z ≠ 0 := by
    intro hz0
    have hy_ne : p.Y ≠ 0 := ProjectivePoint.Y_ne_zero_of_Z_eq_zero p params hp hz0
    rw [hz0, mul_zero] at hy
    exact hy_ne hy
  refine ⟨p.Z, hz_ne, ?_⟩
  ext
  · dsimp [AffinePoint.toProjective, HSMul.hSMul, SMul.smul]
    rw [hx, mul_comm]
  · dsimp [AffinePoint.toProjective, HSMul.hSMul, SMul.smul]
    rw [hy, mul_comm]
  · dsimp [AffinePoint.toProjective, HSMul.hSMul, SMul.smul]
    rw [mul_one]

/-- Bridges `scalarMulProjective` (iterated `circuitStep`) to `bsmul` (standard `nsmulFastE ∘ bitsToNat`). -/
theorem scalarMulProjective_equiv_bsmul {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
    (s : List Bool) (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params) :
    ProjectiveEquiv (scalarMulProjective s params)
      (bsmul s ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) := by
  induction s using List.reverseRecOn with
  | nil =>
    unfold scalarMulProjective pureLoopResult bsmul bitsToNat
    dsimp
    rw [nsmulFastE_zero]
    exact ProjectiveEquiv.refl _
  | append_singleton bs b ih =>
    unfold scalarMulProjective at ih ⊢
    rw [pureLoopResult_append]
    dsimp [pureLoopResult, circuitStep]
    unfold bsmul at ih ⊢
    rw [bitsToNat_append, nsmulFastE_bit]
    dsimp
    have h_dbl : ProjectiveEquiv (doubleE (pureLoopResult infinityPoint bs params) params)
        (doubleE (nsmulFastE (bitsToNat bs) ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) params) :=
      ih.doubleE params
    cases b
    · dsimp
      have h_bs_on : (pureLoopResult infinityPoint bs params).IsOnCurve params :=
        pureLoopResult_on_curve infinityPoint bs params (infinity_on_curve params) h_G
      have h_dbl_on : (doubleE (pureLoopResult infinityPoint bs params) params).IsOnCurve params :=
        doubleE_on_curve _ params h_bs_on
      have h_inf_right : ProjectiveEquiv
          (addE (doubleE (pureLoopResult infinityPoint bs params) params) infinityPoint params)
          (doubleE (pureLoopResult infinityPoint bs params) params) := by
        rw [addE_comm]
        exact addE_infinity_left _ params h_dbl_on.Y_ne_zero
      exact ProjectiveEquiv.trans h_inf_right h_dbl
    · dsimp
      exact h_dbl.addE params (ProjectiveEquiv.refl _)

theorem assert_public_key_sound {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
    (w : Witness F)
    (pk : AffinePoint F)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params)
    (h : ValidPublicKeyWitness w pk params) :
    0 < params.kBits ∧
    ProjectiveEquiv (scalarMulProjective w.bits params) pk.toProjective ∧
    ProjectiveEquiv (bsmul w.bits ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) pk.toProjective := by
  have h_loop : LoopConstraints infinityPoint w.bits w.int_x w.int_y w.int_z params := h.2.2.2.2.1
  have h_assert_eq : AssertEqualProjective (loopResult infinityPoint w.bits w.int_x w.int_y w.int_z params) pk.toProjective := h.2.2.2.2.2.1
  have h_result_eq : loopResult infinityPoint w.bits w.int_x w.int_y w.int_z params = pureLoopResult infinityPoint w.bits params :=
    loopResult_eq_pureLoopResult infinityPoint w.bits w.int_x w.int_y w.int_z params h_loop
  rw [h_result_eq] at h_assert_eq
  have h_on : (pureLoopResult infinityPoint w.bits params).IsOnCurve params :=
    pureLoopResult_on_curve infinityPoint w.bits params (infinity_on_curve params) h_G
  have h_proj : ProjectiveEquiv (scalarMulProjective w.bits params) pk.toProjective :=
    projectiveEquiv_of_assertEqualProjective _ pk params h_on h_assert_eq
  have h_kbits_pos : 0 < params.kBits := by
    by_contra hk0
    have hk_eq : params.kBits = 0 := Nat.eq_zero_of_not_pos hk0
    have hnil : w.bits = [] := List.eq_nil_of_length_eq_zero (h.1.trans hk_eq)
    rw [hnil] at h_assert_eq
    have hy := h_assert_eq.2
    dsimp [pureLoopResult, infinityPoint, AffinePoint.toProjective] at hy
    rw [mul_one, mul_zero] at hy
    exact one_ne_zero hy
  have h_bsmul : ProjectiveEquiv (bsmul w.bits ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) pk.toProjective :=
    ProjectiveEquiv.trans (ProjectiveEquiv.symm (scalarMulProjective_equiv_bsmul w.bits params h_G)) h_proj
  exact ⟨h_kbits_pos, h_proj, h_bsmul⟩

lemma zipLists_map_append_last {F : Type} (bits : List Bool) (wX wY wZ : List F)
    (h_len_X : wX.length = bits.length - 1)
    (h_len_Y : wY.length = bits.length - 1)
    (h_len_Z : wZ.length = bits.length - 1)
    (h_bits_ne : bits ≠ []) :
    (zipLists bits wX wY wZ).map (·.1) ++ [getLastBool bits] = bits := by
  induction bits generalizing wX wY wZ with
  | nil => contradiction
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases wX with
      | nil =>
        cases wY with
        | nil =>
          cases wZ with
          | nil =>
            dsimp [zipLists, getLastBool]
          | cons z zs => dsimp at h_len_Z; omega
        | cons y ys => dsimp at h_len_Y; omega
      | cons x xs => dsimp at h_len_X; omega
    | cons b_next bs_tail =>
      cases wX with
      | nil => dsimp at h_len_X; omega
      | cons x xs =>
        cases wY with
        | nil => dsimp at h_len_Y; omega
        | cons y ys =>
          cases wZ with
          | nil => dsimp at h_len_Z; omega
          | cons z zs =>
            dsimp [zipLists]
            have h_last : getLastBool (b :: b_next :: bs_tail) = getLastBool (b_next :: bs_tail) := rfl
            rw [h_last]
            have h_len_X' : xs.length = (b_next :: bs_tail).length - 1 := by
              simp [List.length] at h_len_X ⊢
              omega
            have h_len_Y' : ys.length = (b_next :: bs_tail).length - 1 := by
              simp [List.length] at h_len_Y ⊢
              omega
            have h_len_Z' : zs.length = (b_next :: bs_tail).length - 1 := by
              simp [List.length] at h_len_Z ⊢
              omega
            have h_ih := ih xs ys zs h_len_X' h_len_Y' h_len_Z' (by simp)
            rw [h_ih]

theorem loopResultZipped_eq_pureLoopResult {F : Type} [Field F] (acc : ProjectivePoint F) (zipped : List (Bool × ProjectivePoint F)) (last_b : Bool) (params : CurveParameters F)
    (h : LoopConstraintsZipped acc zipped params) :
    loopResultZipped acc zipped last_b params = pureLoopResult acc (zipped.map (·.1) ++ [last_b]) params := by
  induction zipped generalizing acc with
  | nil =>
    rfl
  | cons head tail ih =>
    rcases head with ⟨b, w⟩
    dsimp [LoopConstraintsZipped] at h
    rcases h with ⟨⟨tx, ty, tz, h_mux, h_step⟩, h_tail⟩
    dsimp [loopResultZipped]
    rw [ih w h_tail]
    dsimp [pureLoopResult]
    have h_mux_eq := isCircuitBitMuxValid_eq b tx ty tz params h_mux
    have h_step' : circuitStep acc b (if b then params.gx else 0) (if b then params.gy else 1) (if b then 1 else 0) params = w := by
      rw [←h_mux_eq.1, ←h_mux_eq.2.1, ←h_mux_eq.2.2]
      exact h_step
    rw [h_step']

theorem assert_public_key_sound_zipped {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
    (w : Witness F)
    (pk : AffinePoint F)
    (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params)
    (h : ValidPublicKeyWitnessZipped w pk params) :
    0 < params.kBits ∧
    ProjectiveEquiv (scalarMulProjective w.bits params) pk.toProjective ∧
    ProjectiveEquiv (bsmul w.bits ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) pk.toProjective := by
  have h_loop : LoopConstraintsZipped infinityPoint (zipLists w.bits w.int_x w.int_y w.int_z) params := h.2.2.2.2.1
  have h_assert_eq : AssertEqualProjective (loopResultZipped infinityPoint (zipLists w.bits w.int_x w.int_y w.int_z) (getLastBool w.bits) params) pk.toProjective := h.2.2.2.2.2.1
  have h_bits : w.bits ≠ [] := by
    intro hnil
    rw [hnil] at h_assert_eq
    have hz_nil : zipLists ([] : List Bool) w.int_x w.int_y w.int_z = [] := by
      cases w.int_x <;> cases w.int_y <;> cases w.int_z <;> rfl
    rw [hz_nil] at h_assert_eq
    dsimp [getLastBool, loopResultZipped, circuitStep, AffinePoint.toProjective] at h_assert_eq
    rw [doubleE_infinity] at h_assert_eq
    change AssertEqualProjective (addE infinityPoint infinityPoint params) { X := pk.X, Y := pk.Y, Z := 1 } at h_assert_eq
    rw [addE_infinity_infinity] at h_assert_eq
    have hy := h_assert_eq.2
    dsimp [infinityPoint] at hy
    rw [mul_one, mul_zero] at hy
    exact one_ne_zero hy
  have h_kbits_pos : 0 < params.kBits := by
    rw [← h.1]
    exact List.length_pos_iff.mpr h_bits
  have h_result_eq : loopResultZipped infinityPoint (zipLists w.bits w.int_x w.int_y w.int_z) (getLastBool w.bits) params =
    pureLoopResult infinityPoint ((zipLists w.bits w.int_x w.int_y w.int_z).map (·.1) ++ [getLastBool w.bits]) params :=
    loopResultZipped_eq_pureLoopResult infinityPoint (zipLists w.bits w.int_x w.int_y w.int_z) (getLastBool w.bits) params h_loop
  have h_zip_eq : (zipLists w.bits w.int_x w.int_y w.int_z).map (·.1) ++ [getLastBool w.bits] = w.bits := by
    apply zipLists_map_append_last
    · rw [h.1]; exact h.2.1
    · rw [h.1]; exact h.2.2.1
    · rw [h.1]; exact h.2.2.2.1
    · exact h_bits
  rw [h_zip_eq] at h_result_eq
  rw [h_result_eq] at h_assert_eq
  have h_on : (pureLoopResult infinityPoint w.bits params).IsOnCurve params :=
    pureLoopResult_on_curve infinityPoint w.bits params (infinity_on_curve params) h_G
  have h_proj : ProjectiveEquiv (scalarMulProjective w.bits params) pk.toProjective :=
    projectiveEquiv_of_assertEqualProjective _ pk params h_on h_assert_eq
  have h_bsmul : ProjectiveEquiv (bsmul w.bits ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) pk.toProjective :=
    ProjectiveEquiv.trans (ProjectiveEquiv.symm (scalarMulProjective_equiv_bsmul w.bits params h_G)) h_proj
  exact ⟨h_kbits_pos, h_proj, h_bsmul⟩

end Verification
