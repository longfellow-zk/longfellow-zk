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
public import ECDSA.ECBridge
public import ECDSA.Pratt
public import ECDSA.P256NoRoot
public import ECDSA.Secp256k1NoRoot
public import ECDSA.ScalarMulCert

open WeierstrassCurve.Projective

@[expose] public section
section CryptoCurves

/-- Field characteristic prime for Secp256k1 -/
def secp256k1_p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- Fact that secp256k1_p is prime -/
instance : Fact (Nat.Prime secp256k1_p) := ⟨ECDSA.prime_115792089237316195423570985008687907853269984665640564039457584007908834671663⟩

/-- Field characteristic prime for P-256 -/
def p256_p : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

/-- Fact that p256_p is prime -/
instance : Fact (Nat.Prime p256_p) := ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

/-- Group order prime for Secp256k1 -/
def secp256k1_n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Fact that secp256k1_n is prime -/
instance : Fact (Nat.Prime secp256k1_n) := ⟨ECDSA.prime_115792089237316195423570985008687907852837564279074904382605163141518161494337⟩

/-- Group order prime for P-256 -/
def p256_n : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-- Fact that p256_n is prime -/
instance : Fact (Nat.Prime p256_n) := ⟨ECDSA.prime_115792089210356248762697446949407573529996955224135760342422259061068512044369⟩

-- Base fields
abbrev Fq_secp := ZMod secp256k1_p
abbrev Fq_p256 := ZMod p256_p

-- Specific instances for decidability of projective equivalence relation
instance : DecidableRel (α := Fin 3 → Fq_secp) (· ≈ ·) := by
  intro P Q
  change Decidable (∃ u : Fq_secpˣ, u • Q = P)
  infer_instance

instance : DecidableRel (α := Fin 3 → Fq_p256) (· ≈ ·) := by
  intro P Q
  change Decidable (∃ u : Fq_p256ˣ, u • Q = P)
  infer_instance

noncomputable instance {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    DecidablePred (NonsingularLift (W' := W)) :=
  fun _ => Classical.propDecidable _

-- NeZero instances for Fq_secp
instance : NeZero (2 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)
instance : NeZero (3 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)
instance : NeZero (4 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)
instance : NeZero (5 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)
instance : NeZero (6 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)
instance : NeZero (7 : Fq_secp) := NeZero.of_not_dvd (R := Fq_secp) (p := secp256k1_p) (by decide)

-- NeZero instances for Fq_p256
instance : NeZero (2 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)
instance : NeZero (3 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)
instance : NeZero (4 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)
instance : NeZero (5 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)
instance : NeZero (6 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)
instance : NeZero (7 : Fq_p256) := NeZero.of_not_dvd (R := Fq_p256) (p := p256_p) (by decide)

/-- Secp256k1 curve parameters -/
noncomputable def secp256k1_params : CurveParameters Fq_secp := {
  a := 0
  b := 7
  gx := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  gy := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
  kBits := 256
}
/-- P-256 curve parameters -/
noncomputable def p256_params : CurveParameters Fq_p256 := {
  a := -3
  b := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
  gx := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  kBits := 256
}

lemma secp256k1_elliptic : (secp256k1_params.toMathlib).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  rw [isUnit_iff_ne_zero]
  decide

instance : (secp256k1_params.toMathlib).IsElliptic := secp256k1_elliptic

/-- Direct, from the certified fact that the cubic has no root in `F_p` — no point count. -/
instance : CurveHasNoPointsOfOrder2 secp256k1_params where
  no_roots x := by
    have ha : ((ECDSA.sa : ℕ) : ZMod ECDSA.sp) = 0 := by norm_num [ECDSA.sa]
    have hb : ((ECDSA.sb : ℕ) : ZMod ECDSA.sp) = (7 : ZMod ECDSA.sp) := by norm_cast
    have h := ECDSA.secp256k1_cubic_no_root x
    intro hc
    simp only [secp256k1_params] at hc
    refine h ?_
    rw [ha, hb]
    exact hc

lemma p256_elliptic : (p256_params.toMathlib).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  rw [isUnit_iff_ne_zero]
  decide

instance : (p256_params.toMathlib).IsElliptic := p256_elliptic

/-- Direct, from the certified fact that the cubic has no root in `F_p` — no point count. -/
instance : CurveHasNoPointsOfOrder2 p256_params where
  no_roots x := by
    have ha : ((ECDSA.aa : ℕ) : ZMod ECDSA.pp) = -3 := by
      have haa : (ECDSA.aa : ℕ) = ECDSA.pp - 3 := by norm_num [ECDSA.aa, ECDSA.pp]
      rw [haa, Nat.cast_sub (by norm_num [ECDSA.pp]), ZMod.natCast_self]
      push_cast
      ring
    have hb : ((ECDSA.bb : ℕ) : ZMod ECDSA.pp) =
        (0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B : ZMod ECDSA.pp) := by
      norm_cast
    have h := ECDSA.p256_cubic_no_root x
    intro hc
    simp only [p256_params] at hc
    refine h ?_
    rw [ha, hb]
    exact hc

lemma secp256k1_G_on :
    AffinePoint.IsOnCurve { X := secp256k1_params.gx, Y := secp256k1_params.gy } secp256k1_params := by
  unfold AffinePoint.IsOnCurve secp256k1_params
  decide

lemma secp256k1_G_proj_on :
    ProjectivePoint.IsOnCurve
      ({ X := secp256k1_params.gx, Y := secp256k1_params.gy : AffinePoint Fq_secp }).toProjective
      secp256k1_params :=
  affine_to_projective_on_curve _ secp256k1_params secp256k1_G_on

lemma p256_G_on :
    AffinePoint.IsOnCurve { X := p256_params.gx, Y := p256_params.gy } p256_params := by
  unfold AffinePoint.IsOnCurve p256_params
  decide

lemma p256_G_proj_on :
    ProjectivePoint.IsOnCurve
      ({ X := p256_params.gx, Y := p256_params.gy : AffinePoint Fq_p256 }).toProjective
      p256_params :=
  affine_to_projective_on_curve _ p256_params p256_G_on

section GeneratorOrders
set_option maxRecDepth 40000

lemma secp256k1_G_order :
    ProjectiveEquiv
      (bsmul (padBits (natToBits secp256k1_n) secp256k1_params.kBits)
        ({ X := secp256k1_params.gx, Y := secp256k1_params.gy : AffinePoint Fq_secp }).toProjective
        secp256k1_params)
      infinityPoint := by
  refine ECDSA.bsmul_infinity_of_cert (p := secp256k1_p) (a := ECDSA.sa) (b := ECDSA.sb)
    (fuel := 256) secp256k1_params ?_ ?_
    (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)
    _ ?_ (by decide) (by decide)
  · norm_num [ECDSA.sa, secp256k1_params]
  · norm_num [ECDSA.sb, secp256k1_params]
  · unfold ECDSA.castPt secp256k1_params AffinePoint.toProjective
    ext <;> norm_cast

lemma p256_G_order :
    ProjectiveEquiv
      (bsmul (padBits (natToBits p256_n) p256_params.kBits)
        ({ X := p256_params.gx, Y := p256_params.gy : AffinePoint Fq_p256 }).toProjective
        p256_params)
      infinityPoint := by
  refine ECDSA.bsmul_infinity_of_cert (p := p256_p) (a := ECDSA.aa) (b := ECDSA.bb)
    (fuel := 256) p256_params ?_ ?_
    (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
     0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1)
    _ ?_ (by decide) (by decide)
  · have haa : (ECDSA.aa : ℕ) = p256_p - 3 := by norm_num [ECDSA.aa, p256_p]
    rw [haa, Nat.cast_sub (by norm_num [p256_p]), ZMod.natCast_self]
    simp [p256_params]
  · unfold p256_params ECDSA.bb
    norm_cast
  · unfold ECDSA.castPt p256_params AffinePoint.toProjective
    ext <;> norm_cast

end GeneratorOrders

end CryptoCurves
