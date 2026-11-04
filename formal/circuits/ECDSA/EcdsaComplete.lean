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

import ECDSA.Ecdsa

set_option linter.unusedSectionVars false

section ECDSA

variable {F : Type} [Field F] [NeZero (2 : F)] [NeZero (3 : F)] [NeZero (4 : F)] [NeZero (5 : F)] [NeZero (6 : F)] [NeZero (7 : F)]

/--
  Completeness: If a signature verifies under the standard specification,
  AND the completeness gap conditions do NOT hold:
  1. No modulus overflow: R.x < order (meaning r = R.x strictly)
  2. Public key is not zero: PK.x ≠ 0
  3. No exceptional EC addition cases: The intermediate additions during the reconstruction
     (G + PK, R + G, R + PK, and G + (R + PK)) do not result in the point at infinity (i.e.,
     their projective Z-coordinates remain non-zero).
  THEN there exists a valid ZK circuit witness that will verify.

  This theorem formally captures the completeness gap of the circuit by making
  completeness conditional strictly on the absence of these gap cases.

  ### Field Casting & Coercion:
  Signature scalars `(r, s)` and message hash `e` in `StandardEcdsaVerify` are natural
  numbers (`Nat`), bridged to circuit field elements via the canonical ring cast `(· : F)`.
  When `order ≤ char(F)` (as on NIST P-256 and secp256k1), `natCast_ne_zero_of_pos_of_lt_of_le`
  discharges `(r : F) ≠ 0` and `((order - s : Nat) : F) ≠ 0` automatically from `0 < r, s < order`.

  ### Completeness Gap Cases:

  1. The $R.x \ge n$ Case (Modulus Overflow)
    - **Standard Spec**: The signature component $r$ is verified modulo the curve order
    $n$: $r \equiv R.x \pmod n$. Since $R.x \in [0, q-1]$ (where $q$ is the base field
    prime) and $n$ is the curve order, it is possible that $R.x \ge n$. In this case,
    the valid signature has $r = R.x - n$.
    - **Circuit**: The circuit reconstructs $rst$ (which is $r$) and asserts
    `rst = w.rx` (where `w.rx` is $R.x$ as a field element). The reconstructed $rst$
    is constrained to be $< n$ by the range check `rst < n`.
    For this to hold, we must have $R.x < n$. Since $r < n$, this is only possible if
    $r = R.x$. If $R.x \ge n$, then $rst \neq R.x$ since $rst < n \le R.x$, so the
    circuit will **reject** the signature.
    - *Note*: For secp256k1 and P-256, $q - n \approx 2^{127}$, so this happens with
    extremely small probability ($\approx 2^{-128}$), but it is a theoretical incompleteness.

  2. The $PK.x = 0$ Case (Zero X-Coordinate Public Key)
    - **Standard Spec**: The public key $Q_A$ must be a valid curve point and $Q_A \neq \mathcal{O}$.
      It is allowed to have $Q_A.x = 0$ if such a point exists on the curve.
    - **Circuit**: The circuit asserts `pk_x != 0` (via `assert_nonzero(pk_x, w.pk_inv)`).
    - **secp256k1**: The curve equation is $y^2 = x^3 + 7$. If $x=0$, $y^2 = 7$. Since 7 is
      NOT a quadratic residue modulo $q$, there are no valid points with $x=0$. Thus, no
      incompleteness here.
    - **P-256**: $y^2 = x^3 - 3x + b$. If $x=0$, $y^2 = b$. Since $b$ IS a quadratic residue
      modulo $q$, there exist valid public keys with $PK.x = 0$.
      The circuit will **reject** these valid public keys.

  3. The Exceptional Addition Case (Intermediate Point at Infinity)
    - **Standard Spec**: Elliptic curve group operations are defined for all points,
      including the point at infinity $\mathcal{O}$. Standard verification can succeed
      even if intermediate sums (such as $G + PK$, $R + G$, $R + PK$, or $G + (R + PK)$)
      result in $\mathcal{O}$, as long as the final reconstructed point $R$ is not $\mathcal{O}$.
    - **Circuit**: The circuit precomputes representations for these intermediate sums
      and stores them in the witness `w.pre` using only $X$ and $Y$ coordinates (implicitly
      assuming $Z = 1$). It cannot represent $\mathcal{O}$ in `w.pre`.
      Furthermore, the circuit asserts `IsPointEquality` for these precomputations, which
      fails if the Z-coordinate of the projective sum is 0.
      Therefore, the circuit will **reject** the signature if any of the following occur:
      - $PK = -G$ (causing $G + PK = \mathcal{O}$)
      - $R = -G$ (causing $R + G = \mathcal{O}$)
      - $R = -PK$ (causing $R + PK = \mathcal{O}$)
      - $R + PK = -G$ (causing $G + (R + PK) = \mathcal{O}$)
      - *Note*: These exceptional addition cases occur for specific relationships
        between $PK$, $R$, and $G$ (e.g., $PK = -G$, $R = -G$, $R = -PK$, or
        $R = -(PK + G)$). For randomly generated keys and nonces by honest
        parties, the probability of hitting these cases is negligible. However,
        an adversary could intentionally choose $PK = -G$ to trigger this
        completeness gap, causing the circuit to reject a mathematically valid
        signature.

  4. The $order > \mathrm{char}(F)$ Case (Base-Field Modular Wraparound of $r$ or $order - s$)
    - When $order \le \mathrm{char}(F)$ (as on NIST P-256 and secp256k1) or $\mathrm{char}(F) = 0$,
      $0 < r < order$ and $0 < order - s < order$ automatically imply $(r : F) \neq 0$ and
      $((order - s : \mathbb{N}) : F) \neq 0$.
    - On negative-trace curves where $order > \mathrm{char}(F)$, the circuit's non-zero checks
      `w.rx * w.rx_inv = 1` and `sst * w.s_inv = 1` additionally require $(r : F) \neq 0$ and
      $((order - s : \mathbb{N}) : F) \neq 0$ (i.e., $r \neq p$ and $order - s \neq p$).

-/
theorem ecdsa_circuit_completeness
    (pk : AffinePoint F) (e : Nat) (r s : Nat) (order : Nat) (params : CurveParameters F)
    [h_ell : (params.toMathlib).IsElliptic]
    [CurveHasNoPointsOfOrder2 params]
    (h_order_lt : order < 2^params.kBits)
    (h_e_lt : e < 2^params.kBits)
    (h_G : AffinePoint.IsOnCurve { X := params.gx, Y := params.gy } params)
    (h_G_order : ProjectiveEquiv (bsmul (padBits (natToBits order) params.kBits) ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params) infinityPoint)
    (h_std : StandardEcdsaVerify pk e r s order params)
    -- Completeness hypotheses (No-gap conditions)
    (h_no_overflow :
      (r : F) ≠ 0 ∧
      ((order - s : Nat) : F) ≠ 0 ∧
      let G_proj := ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective
      let PK_proj := pk.toProjective
      ∃ (s_inv : Nat), (s * s_inv) % order = 1 ∧
      let z := e % order
      let u1 := (z * s_inv) % order
      let u2 := (r * s_inv) % order
      let u1_G := bsmul (padBits (natToBits u1) params.kBits) G_proj params
      let u2_PK := bsmul (padBits (natToBits u2) params.kBits) PK_proj params
      let R := addE u1_G u2_PK params
      ∃ (R_Z_inv : F), R.Z * R_Z_inv = 1 ∧
      (r : F) = R.X * R_Z_inv ∧
      let rx := R.X * R_Z_inv
      let ry := R.Y * R_Z_inv
      (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 ∧
      (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective params).Z ≠ 0 ∧
      (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z ≠ 0 ∧
      (addE ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective { X := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).X * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Y := (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Y * (addE ({ X := rx, Y := ry : AffinePoint F }).toProjective pk.toProjective params).Z⁻¹, Z := 1 } params).Z ≠ 0
    )
    (h_no_zero_pk : pk.X ≠ 0) :
    ∃ (w : EcdsaWitness F),
      ValidEcdsaWitness w pk (e : F) order params ∧
      natR (w.bi.map val3) = r ∧
      order - natS (w.bi.map val3) = s ∧
      natE (w.bi.map val3) = e := by
  -- 1. Keep copy of h_std and extract
  have h_std_copy := h_std
  rcases h_std with ⟨h_on_pk, h_pk_order, h_r_pos, h_r_lt, h_s_pos, h_s_lt, h_verify⟩

  -- 2. Extract R and R_Z_inv from h_no_overflow
  dsimp at h_no_overflow
  rcases h_no_overflow with ⟨h_r_ne_zero, h_snat_ne_zero, s_inv, hs_inv, hR⟩
  rcases hR with ⟨R_Z_inv, h_RZ, h_r_eq_rx, h_GPK_Z, h_GR_Z, h_RPK_Z, h_GRPK_Z⟩

  -- We need to define s_nat = order - s
  let s_nat := order - s

  have he_lt_k : e < 2^params.kBits := h_e_lt
  have hr_lt_k : r < 2^params.kBits := by omega
  have hs_lt_k : s_nat < 2^params.kBits := by
    dsimp [s_nat]
    omega

  -- 3. Use exists_bi to get bi
  have ⟨bi, h_bi_len, h_bi_bounds, he_eq, hr_eq, hs_eq⟩ := exists_bi e r s_nat he_lt_k hr_lt_k hs_lt_k

  -- Define R_point explicitly
  let G_proj := ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective
  let PK_proj := pk.toProjective

  have h_G_on : ProjectivePoint.IsOnCurve G_proj params :=
    affine_to_projective_on_curve { X := params.gx, Y := params.gy } params h_G

  have h_PK_on : ProjectivePoint.IsOnCurve PK_proj params :=
    affine_to_projective_on_curve pk params h_on_pk

  let z := e % order
  let u1 := (z * s_inv) % order
  let u2 := (r * s_inv) % order
  let u1_G := bsmul (padBits (natToBits u1) params.kBits) G_proj params
  let u2_PK := bsmul (padBits (natToBits u2) params.kBits) PK_proj params
  let R_point := addE u1_G u2_PK params

  -- 4. Use exists_pre_computation to get pre
  let rx := R_point.X * R_Z_inv
  let ry := R_point.Y * R_Z_inv

  have h_R_proj_all := R_point_on_projective_curve pk e r s_inv order params h_on_pk h_G
  dsimp only at h_R_proj_all

  let R_proj : ProjectivePoint F := ({ X := rx, Y := ry : AffinePoint F }).toProjective
  have h_R_proj_equiv : ProjectiveEquiv R_proj R_point := by
    use R_Z_inv
    refine ⟨?_, ?_⟩
    · intro h_zero
      have h_contra : (R_point.Z * R_Z_inv) = 0 := by
        rw [h_zero]
        ring
      rw [h_RZ] at h_contra
      exact one_ne_zero h_contra
    · apply ProjectivePoint.ext
      · dsimp [R_proj, rx, HSMul.hSMul, SMul.smul]
        ring
      · dsimp [R_proj, ry, HSMul.hSMul, SMul.smul]
        ring
      · dsimp [R_proj, HSMul.hSMul, SMul.smul]
        rw [mul_comm, h_RZ]

  have h_R_on : ProjectivePoint.IsOnCurve R_proj params :=
    ProjectiveEquiv.isOnCurve params h_R_proj_equiv h_R_proj_all

  have ⟨pre, h_pre_len, h_pre⟩ := exists_pre_computation pk rx ry params h_GPK_Z h_GR_Z h_RPK_Z h_GRPK_Z

  -- 5. Use exists_loop_witness to get int_x, int_y, int_z
  have ⟨int_x, int_y, int_z, h_len_x, h_len_y, h_len_z, h_loop⟩ := exists_loop_witness bi pk rx ry pre params h_bi_len

  -- 6. Define the witness
  let w : EcdsaWitness F := {
    rx := rx
    ry := ry
    pre := pre
    rx_inv := rx⁻¹
    s_inv := (reconstructS bi)⁻¹
    pk_inv := pk.X⁻¹
    bi := bi.map (fun (x : Nat) => (x : F))
    int_x := int_x
    int_y := int_y
    int_z := int_z
  }

  use w

  have h_w_bi : w.bi = bi.map (fun (x : Nat) => (x : F)) := rfl
  have h_bi_nat : (bi.map (fun (x : Nat) => (x : F))).map val3 = bi :=
    map_val3_cast_eq bi h_bi_bounds

  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 8. Prove ValidEcdsaWitness
    unfold ValidEcdsaWitness

    have h_rx_eq_r : rx = (r : F) := h_r_eq_rx.symm

    have h_w_bi_len_coe : (bi.map (fun (x : Nat) => (x : F))).length = bi.length := by simp

    have h_w_bi_bounds_proof : (∀ v ∈ bi.map (fun (x : Nat) => (x : F)), v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7) :=
      map_cast_bounds bi h_bi_bounds

    have h_w_loop_proof : EcdsaLoopConstraintsF infinityPoint true (bi.map (fun (x : Nat) => (x : F))) w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params :=
      (EcdsaLoopConstraintsF_cast_eq bi h_bi_bounds infinityPoint true
        w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params).mpr h_loop

    refine ⟨(show w.bi.length = params.kBits by rw [h_w_bi, h_w_bi_len_coe]; exact h_bi_len),
            h_len_x, h_len_y, h_len_z, h_pre_len,
            (show ∀ v ∈ w.bi, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 by rw [h_w_bi]; exact h_w_bi_bounds_proof),
            h_pre,
            (show EcdsaLoopConstraintsF infinityPoint true w.bi w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params by
              rw [h_w_bi]
              exact h_w_loop_proof),
            ?_⟩

    have h_pure_eq : ecdsaLoopResult infinityPoint true bi int_x int_y int_z pk rx ry pre params =
                     ecdsaPureLoopResult bi pk rx ry pre params := by
      exact ecdsaLoopResult_eq_ecdsaPureLoopResult infinityPoint true bi int_x int_y int_z pk rx ry pre params h_loop

    have h_inf : (ecdsaPureLoopResult bi pk rx ry pre params).X = 0 ∧ (ecdsaPureLoopResult bi pk rx ry pre params).Z = 0 := by
      have h_R_eq : ∃ (s_inv_o : Nat), ((order - s_nat) * s_inv_o) % order = 1 ∧
        let z := e % order
        let u1 := (z * s_inv_o) % order
        let u2 := (r * s_inv_o) % order
        let G_proj := ({ X := params.gx, Y := params.gy : AffinePoint F }).toProjective
        let PK_proj := pk.toProjective
        let R_std := addE (bsmul (padBits (natToBits u1) params.kBits) G_proj params) (bsmul (padBits (natToBits u2) params.kBits) PK_proj params) params
        ∃ (R_Z_inv_o : F), R_std.Z * R_Z_inv_o = 1 ∧
        rx = R_std.X * R_Z_inv_o ∧ ry = R_std.Y * R_Z_inv_o := by
        use s_inv
        refine ⟨?_, ?_⟩
        · have h_s_eq2 : order - s_nat = s := by dsimp [s_nat]; omega
          rw [h_s_eq2]
          exact hs_inv
        · use R_Z_inv
      have h_s_eq2 : order - s_nat = s := by dsimp [s_nat]; omega
      rw [←h_s_eq2] at h_std_copy
      apply pure_loop_result_is_infinity bi pk rx ry pre params order h_bi_len h_bi_bounds h_pre h_GPK_Z h_GR_Z h_RPK_Z h_GRPK_Z e r s_nat he_eq hr_eq hs_eq h_std_copy h_G_order h_R_eq h_G_on h_PK_on h_R_on

    have h_loop_F_eq : ecdsaLoopResultF infinityPoint true w.bi w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params =
                       ecdsaLoopResult infinityPoint true bi w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params := by
      rw [h_w_bi]
      exact ecdsaLoopResultF_cast_eq bi h_bi_bounds infinityPoint true
        w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params

    have h_final_eq : ecdsaLoopResultF infinityPoint true w.bi w.int_x w.int_y w.int_z pk w.rx w.ry w.pre params =
                       ecdsaPureLoopResult bi pk rx ry pre params := by
      rw [h_loop_F_eq, h_pure_eq]

    refine ⟨?_, ?_, ?_, ?_, h_on_pk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_final_eq]; exact h_inf.1
    · rw [h_final_eq]; exact h_inf.2
    · change reconstructE ((bi.map (fun (x : Nat) => (x : F))).map val3) = (e : F)
      rw [h_bi_nat, reconstructE_eq_natE, he_eq]
    · change reconstructR ((bi.map (fun (x : Nat) => (x : F))).map val3) = rx
      rw [h_bi_nat, reconstructR_eq_natR, hr_eq, h_rx_eq_r]
    · -- IsOnCurve { X := rx, Y := ry } params
      have h_RZ_ne : R_point.Z ≠ 0 := by
        intro h
        rw [h, zero_mul] at h_RZ
        exact one_ne_zero h_RZ.symm
      have h_inv_eq : R_Z_inv = R_point.Z⁻¹ := eq_inv_of_mul_eq_one_right h_RZ
      change ({ X := R_point.X * R_Z_inv, Y := R_point.Y * R_Z_inv } : AffinePoint F).IsOnCurve params
      rw [h_inv_eq]
      exact projective_to_affine_on_curve R_point params h_R_proj_all.1 h_RZ_ne
    · change rx * rx⁻¹ = 1
      apply mul_inv_cancel₀
      rw [h_rx_eq_r]
      exact h_r_ne_zero
    · change reconstructS ((bi.map (fun (x : Nat) => (x : F))).map val3) * (reconstructS bi)⁻¹ = 1
      rw [h_bi_nat]
      apply mul_inv_cancel₀
      rw [reconstructS_eq_natS, hs_eq]
      exact h_snat_ne_zero
    · exact mul_inv_cancel₀ h_no_zero_pk
    · change natR ((bi.map (fun (x : Nat) => (x : F))).map val3) < order
      rw [h_bi_nat, hr_eq]
      exact h_r_lt
    · change natS ((bi.map (fun (x : Nat) => (x : F))).map val3) < order
      rw [h_bi_nat, hs_eq]
      dsimp [s_nat]
      omega
  · rw [h_w_bi, h_bi_nat, hr_eq]
  · rw [h_w_bi, h_bi_nat, hs_eq]
    dsimp [s_nat]
    omega
  · rw [h_w_bi, h_bi_nat, he_eq]

/-- Helper for curves with `order ≤ p` (such as NIST P-256 and secp256k1): any scalar `0 < n < order` casts to a non-zero element of `ZMod p`. -/
lemma natCast_ne_zero_of_pos_of_lt_of_le {p order n : Nat} (h_pos : 0 < n) (h_lt : n < order) (h_le : order ≤ p) :
    (n : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
  have hge : p ≤ n := Nat.le_of_dvd h_pos hdvd
  omega

end ECDSA
