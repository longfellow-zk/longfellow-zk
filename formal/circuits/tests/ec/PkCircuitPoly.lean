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
public import PkCircuit
public import ECDSA.Curves

/-!
# Polynomial Extraction for secp256k1

This module defines symbolic evaluation of a circuit step over multivariate polynomials.
It is used to extract the symbolic polynomials for the next state coordinates.
-/

@[expose] public section

abbrev Fq := Fq_secp

abbrev SymPoly := MvPolynomial String Fq

/-- Algebraic multiplexing -/
def polyMux {F : Type} [CommRing F] (b : F) (valTrue valFalse : F) : F :=
  b * valTrue + (1 - b) * valFalse

/-- Algebraic circuit step evaluating over polynomials -/
def circuitStepPoly {F : Type} [CommRing F] (acc : ProjectivePoint F) (b : F) (params : CurveParameters F) : ProjectivePoint F :=
  let tx := polyMux b params.gx 0
  let ty := polyMux b params.gy 1
  let tz := polyMux b 1 0
  circuitStep acc true tx ty tz params

/-! ### Symbolic Variables Configuration -/

/--
  Symbolic projective point representing the initial accumulator state.
  Coordinates are variables "accX", "accY", "accZ".
-/
noncomputable def sym_acc : ProjectivePoint SymPoly := {
  X := MvPolynomial.X "accX",
  Y := MvPolynomial.X "accY",
  Z := MvPolynomial.X "accZ"
}

/-- Symbolic variable "b" representing the scalar bit. -/
noncomputable def sym_b : SymPoly := MvPolynomial.X "b"

/--
  Secp256k1 curve parameters with symbolic generator coordinates "gx" and "gy".
-/
noncomputable def sym_secp256k1_params : CurveParameters SymPoly := {
  a := 0,
  b := 7,
  gx := MvPolynomial.X "gx",
  gy := MvPolynomial.X "gy",
  kBits := 256
}

/--
  Extracted projective point after one symbolic circuit step.
  Contains the polynomials representing the next X, Y, Z coordinates.
-/
noncomputable def extractedStep : ProjectivePoint SymPoly :=
  circuitStepPoly sym_acc sym_b sym_secp256k1_params

/-! ### Completeness and Concrete 256-Bit Curve Non-Vacuity -/

section NonVacuity

lemma assertEqualProjective_of_projectiveEquiv {F : Type} [Field F]
    (p : ProjectivePoint F) (pk : AffinePoint F)
    (h : ProjectiveEquiv p pk.toProjective) :
    AssertEqualProjective p pk.toProjective := by
  rcases h with ⟨u, _, hp⟩
  have hx : p.X = u * pk.X := congrArg ProjectivePoint.X hp
  have hy : p.Y = u * pk.Y := congrArg ProjectivePoint.Y hp
  have hz : p.Z = u * 1 := congrArg ProjectivePoint.Z hp
  rw [mul_one] at hz
  refine ⟨?_, ?_⟩
  · dsimp [AffinePoint.toProjective]
    rw [hx, hz, mul_one, mul_comm]
  · dsimp [AffinePoint.toProjective]
    rw [hy, hz, mul_one, mul_comm]

def mkPkIntermediates {F : Type} [Field F] :
    ProjectivePoint F → List Bool → CurveParameters F → List (ProjectivePoint F)
  | _, [], _ => []
  | _, [_], _ => []
  | acc, b :: bs@(_ :: _), params =>
      let tx := if b then params.gx else 0
      let ty := if b then params.gy else 1
      let tz := if b then 1 else 0
      let nextAcc := circuitStep acc b tx ty tz params
      nextAcc :: mkPkIntermediates nextAcc bs params

def mkPkWitness {F : Type} [Field F] (bits : List Bool) (params : CurveParameters F) : Witness F :=
  let pts := mkPkIntermediates infinityPoint bits params
  { bits := bits
    int_x := pts.map (·.X)
    int_y := pts.map (·.Y)
    int_z := pts.map (·.Z) }

lemma mkPkIntermediates_length {F : Type} [Field F]
    (acc : ProjectivePoint F) (bits : List Bool) (params : CurveParameters F) :
    (mkPkIntermediates acc bits params).length = bits.length - 1 := by
  induction bits generalizing acc with
  | nil => simp [mkPkIntermediates]
  | cons b bs ih =>
    cases bs with
    | nil => simp [mkPkIntermediates]
    | cons b' bs' =>
      simp [mkPkIntermediates, ih]

lemma mkPkIntermediates_loopConstraints {F : Type} [Field F]
    (acc : ProjectivePoint F) (bits : List Bool) (params : CurveParameters F) :
    LoopConstraints acc bits
      ((mkPkIntermediates acc bits params).map (·.X))
      ((mkPkIntermediates acc bits params).map (·.Y))
      ((mkPkIntermediates acc bits params).map (·.Z))
      params := by
  induction bits generalizing acc with
  | nil => simp [mkPkIntermediates, LoopConstraints]
  | cons b bs ih =>
    cases bs with
    | nil => simp [mkPkIntermediates, LoopConstraints]
    | cons b' bs' =>
      unfold mkPkIntermediates
      dsimp [LoopConstraints]
      refine ⟨if b then params.gx else 0, if b then params.gy else 1, if b then 1 else 0,
        by cases b <;> simp [IsCircuitBitMuxValid], rfl, rfl, rfl, ?_⟩
      exact ih _

lemma mkPkIntermediates_loopConstraintsZipped {F : Type} [Field F]
    (acc : ProjectivePoint F) (bits : List Bool) (params : CurveParameters F) :
    LoopConstraintsZipped acc
      (zipLists bits
        ((mkPkIntermediates acc bits params).map (·.X))
        ((mkPkIntermediates acc bits params).map (·.Y))
        ((mkPkIntermediates acc bits params).map (·.Z)))
      params := by
  induction bits generalizing acc with
  | nil => simp [mkPkIntermediates, zipLists, LoopConstraintsZipped]
  | cons b bs ih =>
    cases bs with
    | nil => simp [mkPkIntermediates, zipLists, LoopConstraintsZipped]
    | cons b' bs' =>
      unfold mkPkIntermediates
      dsimp [zipLists, LoopConstraintsZipped]
      refine ⟨⟨if b then params.gx else 0, if b then params.gy else 1, if b then 1 else 0,
        by cases b <;> simp [IsCircuitBitMuxValid], rfl⟩, ?_⟩
      exact ih _

/-- Completeness for both `ValidPublicKeyWitness` and `ValidPublicKeyWitnessZipped`. -/
theorem assert_public_key_complete {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)]
    (bits : List Bool) (pk : AffinePoint F) (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic] [CurveHasNoPointsOfOrder2 params]
    (h_len : bits.length = params.kBits)
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params)
    (h_pk : pk.IsOnCurve params)
    (h_mul : ProjectiveEquiv
      (bsmul bits ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params)
      pk.toProjective) :
    ValidPublicKeyWitness (mkPkWitness bits params) pk params ∧
    ValidPublicKeyWitnessZipped (mkPkWitness bits params) pk params := by
  have h_bits_ne : bits ≠ [] := by
    intro hnil
    rw [hnil] at h_mul
    unfold bsmul bitsToNat at h_mul
    dsimp at h_mul
    rw [nsmulFastE_zero] at h_mul
    rcases h_mul with ⟨u, hu_ne, hu_eq⟩
    have hz : (0 : F) = u * 1 := congrArg ProjectivePoint.Z hu_eq
    rw [mul_one] at hz
    exact hu_ne hz.symm
  have h_proj : ProjectiveEquiv (scalarMulProjective bits params) pk.toProjective :=
    ProjectiveEquiv.trans (scalarMulProjective_equiv_bsmul bits params h_G) h_mul
  have h_assert : AssertEqualProjective (scalarMulProjective bits params) pk.toProjective :=
    assertEqualProjective_of_projectiveEquiv _ pk h_proj
  let w := mkPkWitness bits params
  have hw_len_x : w.int_x.length = params.kBits - 1 := by
    simp [w, mkPkWitness, mkPkIntermediates_length, h_len]
  have hw_len_y : w.int_y.length = params.kBits - 1 := by
    simp [w, mkPkWitness, mkPkIntermediates_length, h_len]
  have hw_len_z : w.int_z.length = params.kBits - 1 := by
    simp [w, mkPkWitness, mkPkIntermediates_length, h_len]
  have h_loop : LoopConstraints infinityPoint w.bits w.int_x w.int_y w.int_z params :=
    mkPkIntermediates_loopConstraints infinityPoint bits params
  have h_loop_zip : LoopConstraintsZipped infinityPoint (zipLists w.bits w.int_x w.int_y w.int_z) params :=
    mkPkIntermediates_loopConstraintsZipped infinityPoint bits params
  constructor
  · refine ⟨h_len, hw_len_x, hw_len_y, hw_len_z, h_loop, ?_, h_pk⟩
    rw [loopResult_eq_pureLoopResult infinityPoint w.bits w.int_x w.int_y w.int_z params h_loop]
    exact h_assert
  · refine ⟨h_len, hw_len_x, hw_len_y, hw_len_z, h_loop_zip, ?_, h_pk⟩
    rw [loopResultZipped_eq_pureLoopResult infinityPoint _ _ params h_loop_zip]
    have h_zip_eq : (zipLists w.bits w.int_x w.int_y w.int_z).map (·.1) ++ [getLastBool w.bits] = w.bits := by
      apply zipLists_map_append_last
      · rw [hw_len_x]; dsimp [w, mkPkWitness]; rw [h_len]
      · rw [hw_len_y]; dsimp [w, mkPkWitness]; rw [h_len]
      · rw [hw_len_z]; dsimp [w, mkPkWitness]; rw [h_len]
      · exact h_bits_ne
    rw [h_zip_eq]
    exact h_assert

private lemma zmod_mul_eq_of_mod_eq {p x y z : Nat} (h : (x * y) % p = z % p) :
    (x : ZMod p) * (y : ZMod p) = (z : ZMod p) := by
  rw [← Nat.cast_mul, ← ZMod.natCast_mod (x * y) p, h, ZMod.natCast_mod]

def secp256k1_test_pk_x : Nat := 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
def secp256k1_test_pk_y : Nat := 0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a

def secp256k1_test_pk : AffinePoint Fq_secp :=
  { X := (secp256k1_test_pk_x : Fq_secp)
    Y := (secp256k1_test_pk_y : Fq_secp) }

private lemma secp256k1_test_pk_on : secp256k1_test_pk.IsOnCurve secp256k1_params := by
  unfold AffinePoint.IsOnCurve secp256k1_test_pk secp256k1_params
  decide

/-- Concrete 256-bit non-vacuity of `assert_public_key_complete`, `assert_public_key_sound`,
    and `assert_public_key_sound_zipped` on deployed `secp256k1_params` (`PK = [2]G`). -/
theorem secp256k1_pk_circuit_non_vacuous :
    ∃ (w : Witness Fq_secp) (pk : AffinePoint Fq_secp),
      ValidPublicKeyWitness w pk secp256k1_params ∧
      ValidPublicKeyWitnessZipped w pk secp256k1_params ∧
      0 < secp256k1_params.kBits ∧
      ProjectiveEquiv (scalarMulProjective w.bits secp256k1_params) pk.toProjective ∧
      ProjectiveEquiv
        (bsmul w.bits ({ X := secp256k1_params.gx, Y := secp256k1_params.gy : AffinePoint Fq_secp }).toProjective secp256k1_params)
        pk.toProjective := by
  let bits := padBits (natToBits 2) secp256k1_params.kBits
  have h_len : bits.length = secp256k1_params.kBits :=
    padBits_length (natToBits 2) secp256k1_params.kBits
      (natToBits_length 2 256 (by decide))
  let g_tri : ECDSA.Tri :=
    (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)
  have h_cast_g : ECDSA.castPt g_tri =
      ({ X := secp256k1_params.gx, Y := secp256k1_params.gy : AffinePoint Fq_secp }).toProjective := by
    unfold ECDSA.castPt g_tri secp256k1_params AffinePoint.toProjective
    ext <;> norm_cast
  have ha : ((ECDSA.sa : ℕ) : Fq_secp) = secp256k1_params.a := by norm_num [ECDSA.sa, secp256k1_params]
  have hb : ((ECDSA.sb : ℕ) : Fq_secp) = secp256k1_params.b := by norm_num [ECDSA.sb, secp256k1_params]
  let pt2 := ECDSA.nsmulNat secp256k1_p ECDSA.sa ECDSA.sb 2 2 g_tri
  have h_mul : ProjectiveEquiv
      (bsmul bits ({ X := secp256k1_params.gx, Y := secp256k1_params.gy : AffinePoint Fq_secp }).toProjective secp256k1_params)
      secp256k1_test_pk.toProjective := by
    unfold bits bsmul
    rw [bitsToNat_padBits, ← h_cast_g, ← ECDSA.castPt_nsmulNat secp256k1_params ha hb g_tri 2 2 (by decide)]
    have hz : (pt2.2.2 : Fq_secp) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff pt2.2.2 secp256k1_p).mp h0
      exact (by decide : pt2.2.2 % secp256k1_p ≠ 0) (Nat.mod_eq_zero_of_dvd hdvd)
    refine ⟨(pt2.2.2 : Fq_secp), hz, ?_⟩
    unfold ECDSA.castPt secp256k1_test_pk AffinePoint.toProjective
    ext
    · dsimp [HSMul.hSMul, SMul.smul]
      exact (zmod_mul_eq_of_mod_eq (p := secp256k1_p) (x := pt2.2.2) (y := secp256k1_test_pk_x) (z := pt2.1) (by decide)).symm
    · dsimp [HSMul.hSMul, SMul.smul]
      exact (zmod_mul_eq_of_mod_eq (p := secp256k1_p) (x := pt2.2.2) (y := secp256k1_test_pk_y) (z := pt2.2.1) (by decide)).symm
    · dsimp [HSMul.hSMul, SMul.smul]
      rw [mul_one]
  obtain ⟨hw, hw_zip⟩ := assert_public_key_complete bits secp256k1_test_pk secp256k1_params
    h_len secp256k1_G_on secp256k1_test_pk_on h_mul
  obtain ⟨hk, h_proj, h_bsmul⟩ := assert_public_key_sound (mkPkWitness bits secp256k1_params)
    secp256k1_test_pk secp256k1_params secp256k1_G_on hw
  have _ := assert_public_key_sound_zipped (mkPkWitness bits secp256k1_params)
    secp256k1_test_pk secp256k1_params secp256k1_G_on hw_zip
  exact ⟨mkPkWitness bits secp256k1_params, secp256k1_test_pk, hw, hw_zip, hk, h_proj, h_bsmul⟩

def p256_pk_test_x : Nat := 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
def p256_pk_test_y : Nat := 0x7775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1

def p256_pk_test : AffinePoint Fq_p256 :=
  { X := (p256_pk_test_x : Fq_p256)
    Y := (p256_pk_test_y : Fq_p256) }

private lemma p256_pk_test_on : p256_pk_test.IsOnCurve p256_params := by
  unfold AffinePoint.IsOnCurve p256_pk_test p256_params
  decide

/-- Concrete 256-bit non-vacuity of `assert_public_key_complete`, `assert_public_key_sound`,
    and `assert_public_key_sound_zipped` on deployed `p256_params` (`PK = [2]G`). -/
theorem p256_pk_circuit_non_vacuous :
    ∃ (w : Witness Fq_p256) (pk : AffinePoint Fq_p256),
      ValidPublicKeyWitness w pk p256_params ∧
      ValidPublicKeyWitnessZipped w pk p256_params ∧
      0 < p256_params.kBits ∧
      ProjectiveEquiv (scalarMulProjective w.bits p256_params) pk.toProjective ∧
      ProjectiveEquiv
        (bsmul w.bits ({ X := p256_params.gx, Y := p256_params.gy : AffinePoint Fq_p256 }).toProjective p256_params)
        pk.toProjective := by
  let bits := padBits (natToBits 2) p256_params.kBits
  have h_len : bits.length = p256_params.kBits :=
    padBits_length (natToBits 2) p256_params.kBits
      (natToBits_length 2 256 (by decide))
  let g_tri : ECDSA.Tri :=
    (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
     0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1)
  have h_cast_g : ECDSA.castPt g_tri =
      ({ X := p256_params.gx, Y := p256_params.gy : AffinePoint Fq_p256 }).toProjective := by
    unfold ECDSA.castPt g_tri p256_params AffinePoint.toProjective
    ext <;> norm_cast
  have ha : ((ECDSA.aa : ℕ) : Fq_p256) = p256_params.a := by
    have haa : (ECDSA.aa : ℕ) = p256_p - 3 := by norm_num [ECDSA.aa, p256_p]
    rw [haa, Nat.cast_sub (by norm_num [p256_p]), ZMod.natCast_self]
    simp [p256_params]
  have hb : ((ECDSA.bb : ℕ) : Fq_p256) = p256_params.b := by
    unfold p256_params ECDSA.bb
    norm_cast
  let pt2 := ECDSA.nsmulNat p256_p ECDSA.aa ECDSA.bb 2 2 g_tri
  have h_mul : ProjectiveEquiv
      (bsmul bits ({ X := p256_params.gx, Y := p256_params.gy : AffinePoint Fq_p256 }).toProjective p256_params)
      p256_pk_test.toProjective := by
    unfold bits bsmul
    rw [bitsToNat_padBits, ← h_cast_g, ← ECDSA.castPt_nsmulNat p256_params ha hb g_tri 2 2 (by decide)]
    have hz : (pt2.2.2 : Fq_p256) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff pt2.2.2 p256_p).mp h0
      exact (by decide : pt2.2.2 % p256_p ≠ 0) (Nat.mod_eq_zero_of_dvd hdvd)
    refine ⟨(pt2.2.2 : Fq_p256), hz, ?_⟩
    unfold ECDSA.castPt p256_pk_test AffinePoint.toProjective
    ext
    · dsimp [HSMul.hSMul, SMul.smul]
      exact (zmod_mul_eq_of_mod_eq (p := p256_p) (x := pt2.2.2) (y := p256_pk_test_x) (z := pt2.1) (by decide)).symm
    · dsimp [HSMul.hSMul, SMul.smul]
      exact (zmod_mul_eq_of_mod_eq (p := p256_p) (x := pt2.2.2) (y := p256_pk_test_y) (z := pt2.2.1) (by decide)).symm
    · dsimp [HSMul.hSMul, SMul.smul]
      rw [mul_one]
  obtain ⟨hw, hw_zip⟩ := assert_public_key_complete bits p256_pk_test p256_params
    h_len p256_G_on p256_pk_test_on h_mul
  obtain ⟨hk, h_proj, h_bsmul⟩ := assert_public_key_sound (mkPkWitness bits p256_params)
    p256_pk_test p256_params p256_G_on hw
  have _ := assert_public_key_sound_zipped (mkPkWitness bits p256_params)
    p256_pk_test p256_params p256_G_on hw_zip
  exact ⟨mkPkWitness bits p256_params, p256_pk_test, hw, hw_zip, hk, h_proj, h_bsmul⟩

end NonVacuity

