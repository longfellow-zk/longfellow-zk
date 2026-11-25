import LfzkV1.SignatureResponse125

/-! Charge failure of the response-guided signature extractor along the
actual signature verifier path. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

namespace LfzkV1.SignatureResponsePath125

open Finset Merkle.MH
open LfzkV1.CompiledZk LfzkV1.CompiledLongfellow LfzkV1.CompiledLongfellowAdaptive
open LfzkV1.CertifiedV1 LfzkV1.RbrZkLongfellow LfzkV1.RbrZkSplit LfzkV1.RbrZkFlat
open LfzkV1.RbrLayerStepS LfzkV1.NizkDeployedHash LfzkV1.NizkZk LfzkV1.SignatureResponse125
open scoped Classical

variable {C F Msg D Enc Salt X Ctx Out : Type} [Fintype C] [DecidableEq C]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
  [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
  [DecidableEq Msg] [Inhabited Msg]
  {M nt nlin : ℕ} {hR : v7SigHahn.Valid}
  {codec : Codec Salt (Col F v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
  {dec : RoleDecoders codec}
variable (S : CircuitSide v7SigHahn hR v7SigHahn_openings_pos 8 C F Msg M nt nlin X dec Prod.snd)

local notation "R" => v7SigHahn
local notation "u" => Rounds.Role.layerBase v7SigHahn.params.rounds v7SigHahn.params.nl + 1
local notation "Len" => Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds
local notation "SigPoint" => MPoint Ctx Msg v7SigHahn.params.nl v7SigHahn.params.rounds
local notation "Side" => S.toSide.toZkSide
private noncomputable abbrev pathChain (σ : Sig D C X Enc) (ms : ℕ → Msg) :=
  chain (nl := (R).params.nl) (w := (R).params.rounds)
    ((Side).V σ) ((Side).H σ) ((Side).asg σ) ((Side).Sat σ) (flatData ((Side).LD σ)) ms

/-- A failure pays either at one field transition of the recovered
candidate, or at the combination challenge and the actual opening. -/
theorem trace_pays (σ : Sig D C X Enc) (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : SigPoint → C)
    (hacc : let tape : Fin Len → C := fun i => ro (msgPoint ctx msgOf out i.val)
      ZkLayerStepAccepts .accepted .start (steps ((Side).V σ) ((Side).LD σ) (msgOf out)) tape)
    (hnone : let tape : Fin Len → C := fun i => ro (msgPoint ctx msgOf out i.val)
      signatureResponseWitness S σ (msgOf out) tape = none) :
    1 ≤ ∑ j : Fin Len,
      let p := msgPoint ctx msgOf out j.val
      pointCharge S σ p (mpoints.chal ro p) (ro p) := by
  let tape : Fin Len → C := fun j => ro (msgPoint ctx msgOf out j.val)
  let charge (j : Fin Len) :=
    let p := msgPoint ctx msgOf out j.val
    pointCharge S σ p (mpoints.chal ro p) (ro p)
  let V := (Side).V σ
  let LD := (Side).LD σ
  let P := S.toSide.terminalPotential σ LfzkV1.GradedSignature.curve
  let ms := msgOf out
  obtain ⟨sys, hb, hq⟩ := (zkAccepts_iff V ms
    (fun m pref => LD.accepting m pref (ms m)) tape).mp hacc
  have hf := zkBuilt_fits V ms tape hb
  have hs : (pathChain S σ ms).state u (Bcs.trunc tape u fieldLen_le) = .built sys := by
    have h1 : (pathChain S σ ms).state u (Bcs.trunc tape u fieldLen_le) =
        (zkRun (nl := (R).params.nl) (w := (R).params.rounds) V ms
          (fun m pref => LD.accepting m pref (ms m))).state u (Bcs.trunc tape u fieldLen_le) :=
      state_eq_of _ _ rfl rfl _ _
    rw [h1, zk_state_acc_congr V ms _ (fun _ _ _ _ => ∅) _ (by omega)]
    exact builtOf_eq_some.mp hb
  apply Bcs.PotentialChain.one_or_two_slots_pay charge (fun j => pointCharge_nonneg S σ _ _ _)
  rcases signatureResponseWitness_none_cases S σ ms tape sys hf hnone with hfail | ⟨x, hx, hw⟩
  · right
    let ic : Fin Len := ligIdx
    let iq : Fin Len := qryIdx
    let pc : SigPoint := msgPoint ctx msgOf out ic.val
    let pq : SigPoint := msgPoint ctx msgOf out iq.val
    have hic : ic.val = u := rfl
    have hiq : iq.val = u + 1 := rfl
    have hsc : pc.role.slot = u := (slot_msgPoint ctx msgOf out ic.isLt).trans hic
    have hsq : pq.role.slot = u + 1 := (slot_msgPoint ctx msgOf out iq.isLt).trans hiq
    have hpc := sidePoint_built_state_of_verifier (H := (Side).H σ) (Sat := (Side).Sat σ)
      LD ctx msgOf out ro ic (by omega) sys hs
    have hpq := sidePoint_built_state_of_verifier (H := (Side).H σ) (Sat := (Side).Sat σ)
      LD ctx msgOf out ro iq (by omega) sys hs
    have hpref : ∀ j : Fin pq.role.slot,
        mpoints.chal ro pq j = Bcs.trunc tape (u + 1) queryLen_le (Fin.cast hsq j) := by
      intro j
      change ro (mpoints.anc pq j.val) = ro (msgPoint ctx msgOf out j.val)
      exact congrArg ro (anc_msgPoint ctx msgOf out (by have := j.isLt; omega) iq.isLt)
    have hmsgq : pq.msgFn pq.role.slot = ms (u + 1) := by
      rw [hsq]
      exact msgFn_msgPoint ctx msgOf out iq.isLt (by omega)
    have hlate : u < pq.role.slot := by omega
    let pref : Fin pq.role.slot → C := mpoints.chal ro pq
    have hchall : pref ⟨u, hlate⟩ = tape ic := by
      rw [show pref ⟨u, hlate⟩ = _ from hpref ⟨u, hlate⟩]
      exact congrArg tape (Fin.ext hic.symm)
    have haccept : V.decodeQuery (ro pq) ∈ LD.accepting pq.role.slot (mpoints.chal ro pq)
        (pq.msgFn pq.role.slot) sys (V.decodeChal (tape ic)) := by
      have hset := accepting_eq_of_prefix LD.accepting hsq (mpoints.chal ro pq)
        (Bcs.trunc tape (u + 1) queryLen_le) hpref hmsgq sys (rfl : V.decodeChal (tape ic) = _)
      rw [hset]
      exact hq
    have hc : charge ic = P.weight sys (V.decodeChal (tape ic)) := by
      change pointCharge S σ pc (mpoints.chal ro pc) (ro pc) = _
      exact pointCharge_batch_eq S σ pc _ _ sys hsc hpc
    have hqc : charge iq = 1 - P.weight sys (V.decodeChal (tape ic)) := by
      have hfailed : failedAt S σ sys (V.decodeChal (pref ⟨u, hlate⟩)) (pq.msgFn pq.role.slot) := by
        rw [hchall, hmsgq]
        exact hfail
      have hquery : V.decodeQuery (ro pq) ∈
          LD.accepting pq.role.slot pref (pq.msgFn pq.role.slot) sys (V.decodeChal (pref ⟨u, hlate⟩)) := by
        rw [hchall]
        exact haccept
      exact (pointCharge_opening_eq S σ pq pref (ro pq) sys hlate hpq hfailed hquery).trans
        (congrArg (fun coin => 1 - P.weight sys (V.decodeChal coin)) hchall)
    refine ⟨ic, iq, fun h => ?_, ?_⟩
    · have hh := congrArg Fin.val h
      omega
    · rw [hc, hqc]
      linarith only []
  · left
    obtain ⟨i, hi, a, h0, h1⟩ := candidate_field_escape_of_built (H := (Side).H σ)
      (Sat := (Side).Sat σ) (flatData LD) ms tape x hw sys hs hx
    let wrong (msgs : ℕ → Msg) (j : ℕ) (pref : Fin j → C) :=
      (pathChain S σ msgs).Wrong a ((pathChain S σ msgs).state j pref)
    have hp := shed_at_msgPoint_of wrong
      (fun msgs msgs' j h pref => by
        unfold wrong pathChain
        have loc := zkChain_msgLocal (nl := (R).params.nl) (w := (R).params.rounds)
          V ((Side).H σ) ((Side).asg σ) ((Side).Sat σ) (flatData LD)
        rw [state_congrG loc j h pref, loc.wrong msgs msgs'])
      ctx msgOf out ro i h0 h1
    let pt : SigPoint := msgPoint ctx msgOf out i.val
    have hslot : pt.role.slot = i.val := slot_msgPoint ctx msgOf out i.isLt
    have he : candidateEscape (pathChain S σ pt.msgFn) pt.role.index (mpoints.chal ro pt) (ro pt) :=
      ⟨a, hp.1, hp.2⟩
    refine ⟨i, ?_⟩
    change 1 ≤ pointCharge S σ pt (mpoints.chal ro pt) (ro pt)
    rw [pointCharge_field_of S σ pt _ _ (show pt.role.slot < u by omega) he]

end LfzkV1.SignatureResponsePath125
