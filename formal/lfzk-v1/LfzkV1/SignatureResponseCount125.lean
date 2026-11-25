import LfzkV1.SignatureResponsePath125
import LfzkV1.TwoFieldCover125

/-! Apply the shared signature accounting to actual response decoding. -/

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace LfzkV1.SignatureResponse125

open Finset Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Bcs.TotalOracle
open LfzkV1.CertifiedV1 LfzkV1.CompiledZk LfzkV1.CompiledLongfellow
  LfzkV1.CompiledLongfellowAdaptive LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField
  LfzkV1.TwoFieldCover125 LfzkV1.NizkGrinding
open scoped Classical

variable {C K D Enc Early Public MsgH Msg Out F Salt : Type}
variable [Fintype C] [DecidableEq C] [Nonempty C]
  [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [DecidableEq Early]
  [Inhabited MsgH] [DecidableEq MsgH] [Inhabited Msg] [DecidableEq Msg]
  [Fintype D] [Fintype K] [Fintype Early] [Fintype MsgH] [Fintype Msg]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F] [Inhabited Salt]
variable {M nt nlin : ℕ} {hS : v7SigHahn.Valid}
variable {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {dec : RoleDecoders codec} {R : Row}

local notation "Pt" => SignatureBudget125.PairPoint D K Early MsgH Msg R
local notation "SPoint" => SignaturePoint D K Early MsgH Msg R
variable (Side : CircuitSide v7SigHahn hS v7SigHahn_openings_pos 8 C F Msg M nt nlin Public dec Prod.snd)
variable (represent : K → C) (pubAt : SignaturePoint D K Early MsgH Msg R → Public)

private noncomputable def combinedCharge (κ : Cut D Enc) (p : Pt) (H : Pt → C) (coin : C) : ℚ :=
  match p with
  | Sum.inr (Sum.inr q) =>
    pointCharge Side (κ, represent q.ctx.1.2.1, pubAt q) q
      (mpoints.chal (fun p' => H (Sum.inr (Sum.inr p'))) q) coin
  | _ => 0

private theorem combinedCharge_nonneg (κ : Cut D Enc) (p : Pt) (H : Pt → C) (coin : C) :
    0 ≤ combinedCharge Side represent pubAt κ p H coin := by
  rcases p with p | p | p
  · exact le_rfl
  · exact le_rfl
  · exact pointCharge_nonneg Side _ _ _ _

private theorem combinedCharge_local (κ : Cut D Enc) (p : Pt) (H : Pt → C) :
    (∑ coin : C, combinedCharge Side represent pubAt κ p H coin) ≤ signatureRawBudget (C := C) p := by
  rcases p with p | p | p
  · change (∑ _ : C, (0 : ℚ)) ≤ 0
    simp only [sum_const_zero, le_refl]
  · change (∑ _ : C, (0 : ℚ)) ≤ 0
    simp only [sum_const_zero, le_refl]
  · exact pointCharge_local Side _ _ _

private theorem combinedCharge_off (κ : Cut D Enc) (p : Pt) (H H' : Pt → C)
    (h : AgreeOff p H H') (coin : C) :
    combinedCharge Side represent pubAt κ p H coin = combinedCharge Side represent pubAt κ p H' coin := by
  rcases p with p | p | p
  · rfl
  · rfl
  · have hpref :
        mpoints.chal (fun q : SPoint => H (Sum.inr (Sum.inr q))) p =
          mpoints.chal (fun q : SPoint => H' (Sum.inr (Sum.inr q))) p := by
      apply mpoints.chal_congr (q := p)
      intro q hq
      exact h _ (fun he => hq (Sum.inr.inj (Sum.inr.inj he)))
    dsimp only [combinedCharge]
    rw [hpref]

/-- The original signature budget also bounds failure of the actual
response-assisted decoder, with one joint observed-query ledger. -/
theorem signature_response_failure_count_le {fc tA N TM : ℕ}
    (body : TwoOracleTree Enc D Pt C Out tA N) (check : Out → Tree Enc D Unit fc)
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (sigPubOf : Out → Public) (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → Msg)
    (hpub : ∀ out (j : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds)),
      pubAt (msgPoint (ctxOf rootH rootS avOf earlyOf out, fun j => msgH out j.val) msgS out j.val) =
        sigPubOf out)
    (claimS : Out → OpeningClaim v7SigHahn.params.row.n Salt
      (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (mt : Fin TM → D) (event : (Pt → C) → Prop)
    (hfail : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H → signatureResponseWitness Side (sideCtx S (represent ∘ avOf) sigPubOf mt H)
        (msgS (S.proof mt H)) (slice2 R v7SigHahn (S.challenges mt H)) = none)
    (hacc : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H → Side.toSide.acceptsDH S check rootS msgS claimS
        (represent ∘ avOf) sigPubOf (slice2 R v7SigHahn) mt H)
    (hexp : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H → S.Explains dec Prod.snd claimS mt H) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ ((1426 : ℚ) / (1000 * 2^128)) * ∑ H : Pt → C,
      ((observedRole (S.search mt) .signature H).card + (1 : ℚ)) := by
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  refine signature_count_of_charge S (combinedCharge Side represent pubAt)
    (combinedCharge_nonneg Side represent pubAt) (combinedCharge_local Side represent pubAt)
    (combinedCharge_off Side represent pubAt) mt
    (setup2_hashInput_injective body rootH rootS avOf earlyOf msgH msgS)
    (signature_raw_budget_replay_le rootH rootS avOf earlyOf msgH msgS) event ?_
  intro H hevent
  let out := S.proof mt H
  let σ := sideCtx S (represent ∘ avOf) sigPubOf mt H
  let ctx := (ctxOf rootH rootS avOf earlyOf out, fun j : Fin (Rounds.Role.length R.params.nl R.params.rounds) =>
    msgH out j.val)
  let sideRO (q : SPoint) := H (Sum.inr (Sum.inr q))
  have ha := Side.toSide.hrightDH_of_accepts S check rootS (fun _ => rfl) msgS
    claimS (represent ∘ avOf) sigPubOf (slice2 R v7SigHahn) mt H (hacc H hevent) (hexp H hevent)
  have ht : slice2 R v7SigHahn (S.challenges mt H) =
      fun j : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) =>
        sideRO (msgPoint ctx msgS out j.val) := by
    funext j
    change H (hash2 rootH rootS avOf earlyOf msgH msgS out
      (1 + Rounds.Role.length R.params.nl R.params.rounds + j.val)) = _
    rw [hash2_side2]
  rw [ht] at ha
  have hn := hfail H hevent
  change signatureResponseWitness Side σ (msgS out) (slice2 R v7SigHahn (S.challenges mt H)) = none at hn
  rw [ht] at hn
  have hpay := SignatureResponsePath125.trace_pays Side σ ctx msgS out sideRO ha hn
  let charge (p : Pt) := combinedCharge Side represent pubAt (S.context mt H) p H (H p)
  change 1 ≤ ∑ j : Fin _, charge (hash2 rootH rootS avOf earlyOf msgH msgS out j.val)
  rw [sum_hash2 rootH rootS avOf earlyOf msgH msgS out charge]
  change 1 ≤ 0 + (∑ _ : Fin (Rounds.Role.length R.params.nl R.params.rounds), (0 : ℚ)) +
    ∑ j : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
      charge (Sum.inr (Sum.inr (msgPoint ctx msgS out j.val)))
  simp only [sum_const_zero, zero_add]
  refine hpay.trans_eq ?_
  apply sum_congr rfl
  intro j _
  let q : SPoint := msgPoint ctx msgS out j.val
  have hσ : (S.context mt H, represent q.ctx.1.2.1, pubAt q) = σ := by
    change (S.context mt H, represent (avOf out), pubAt q) =
      (S.context mt H, represent (avOf out), sigPubOf out)
    rw [hpub out j]
  change pointCharge Side σ q (mpoints.chal sideRO q) (sideRO q) =
    pointCharge Side (S.context mt H, represent q.ctx.1.2.1, pubAt q) q (mpoints.chal sideRO q) (sideRO q)
  rw [hσ]

end LfzkV1.SignatureResponse125
