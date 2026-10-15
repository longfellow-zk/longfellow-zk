import Lfzk.CertifiedHahn
import Lfzk.Mac

/-!
# Checks behind the soundness audit

The lower bounds below are on this analysis's error expressions, not on an adversary's success.
They prevent interpreting a failed numerical certificate as an attack or a security upper bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.SoundnessAudit

open Polynomial Finset Lfzk.CertifiedV1 Lfzk.NizkZk

/-- Equal public tags at a nonzero multiplier do not force equal messages when the two
private blinds differ. This refutes dropping the shared-blind premise from the existing MAC
composition, not the security of the protocol with blinds committed before the challenge. -/
theorem separate_blinds_collision {F : Type} [Field F] :
    Lfzk.Mac.macTag (1 : F) (fun _ : Fin 1 => 0) (fun _ => 0) =
      Lfzk.Mac.macTag (1 : F) (fun _ : Fin 1 => -1) (fun _ => 1) ∧
    (fun _ : Fin 1 => (0 : F)) ≠ (fun _ => 1) ∧ (1 : F) ≠ 0 := by
  simp [Lfzk.Mac.macTag, funext_iff]

/-- The initial hash-side decoder cannot meet the theorem's exact-balance premises if
its raw coin is just a 256-bit digest. Even the smallest v7 output point needs five
GF(2^128) elements. This concerns exact uniformity, not computational pseudorandomness. -/
theorem no_256bit_init_decoder {C F : Type*} [Fintype C] [Nonempty C] [Fintype F] [DecidableEq F]
    (hC : Fintype.card C = 2 ^ 256) (hF : Fintype.card F = 2 ^ 128)
    (decode : C → (Fin 3 → F) × F × F) (k : ℕ)
    (hbal : ∀ y, (univ.filter fun c => decode c = y).card ≤ k) :
    ¬ k * Fintype.card F ^ (3 + 2) ≤ Fintype.card C := by
  classical
  let c : C := Classical.choice inferInstance
  have hpos : 0 < (univ.filter fun c' => decode c' = decode c).card :=
    card_pos.mpr ⟨c, by simp⟩
  have hk : 0 < k := hpos.trans_le (hbal (decode c))
  intro h
  rw [hC, hF] at h
  norm_num at h
  omega

/-- A quadratic can have two distinct roots while its Boolean sum is nonzero, even in
characteristic two. Thus the generic sumcheck root count cannot be reduced from two to one
merely because a false incoming claim forces a nonzero Boolean sum. -/
theorem quadratic_two_roots {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    let p : Polynomial F := X * (X - C a)
    p.eval 0 + p.eval 1 ≠ 0 ∧ (univ.filter fun r : F => p.eval r = 0).card = 2 := by
  dsimp only
  constructor
  · simpa using sub_ne_zero.mpr (Ne.symm ha1)
  · have hroots : (univ.filter fun r : F => (X * (X - C a) : Polynomial F).eval r = 0)
        = {0, a} := by
      ext r
      simp [mul_eq_zero, sub_eq_zero]
    rw [hroots]
    simp [Ne.symm ha0]

/-- The current hash cores all exceed 2^-116: the 115-bit two-field headline cannot be
rounded up by improving the signature side alone. -/
theorem hash_core_exceeds_116 :
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash1 3 v7Hash1.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash2 4 v7Hash2.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash3 4 v7Hash3.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash4 5 v7Hash4.cardCand := by
  native_decide

/-- Even with zero Ligero error, the present list-weighted sumcheck union bound alone
exceeds 2^-117 at every hash profile. Improving only Ligero can at best reach 116 integer bits
with this accounting. This is a limitation of the bound, not a security upper bound. -/
theorem hash_round_charge_exceeds_117 :
    ∀ R ∈ [v7Hash1, v7Hash2, v7Hash3, v7Hash4],
      (1 : ℚ) / 2 ^ 117 <
        (R.cardCand * R.params.totalRounds * 2 : ℕ) / (R.params.row.fieldSize : ℚ) := by
  native_decide

/-- The new row strictly improves the signature summand of the two-field core. -/
theorem signature_core_improves :
    zkCoreAt v7SigHahn 8 v7SigHahn.cardCand < zkCoreAt v7Sig 8 v7Sig.cardCand := by
  native_decide

end Lfzk.SoundnessAudit
