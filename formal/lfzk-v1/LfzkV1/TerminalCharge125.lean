import LfzkV1.TerminalPrefix125
import LfzkV1.TwoFieldCover125
import LfzkV1.CompiledZkDeployedHash
import LfzkV1.HashCircuitReplay125

/-!
# Terminal response charges for an actual two-field search

A fixed Merkle tape and the prefix through input binding determine the
Ligero instance read at the batching point. The two terminal answers can
change without changing that instance. A valid opening is encoded by its
complete decoded response at the same prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace LfzkV1.TerminalCharge125

open Bcs Bcs.TotalOracleCommit Bcs.TotalOracle Finset Merkle.RandomOracle
open Merkle.RandomOracle.TwoOracleTree LigeroFamily CodingTheory
open LfzkV1.CompiledZk LfzkV1.CompiledZkDeployedHash LfzkV1.RbrZkLongfellow
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField LfzkV1.NizkGrinding
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.TerminalPrefix125 LfzkV1.TwoFieldCover125 LfzkV1.TwoFieldV1Rows
open scoped Classical

variable {D K Early Msg SigMsg C Enc Out : Type} [Inhabited Msg] [Inhabited SigMsg]
variable {nl nlS : ℕ} {w wS : ℕ → ℕ}
local notation "Pt" => Pt2 D K Early Msg SigMsg nl nlS w wS
local notation "Prefix" => BatchPrefix (SideCtx D K Early) Msg nl w
local notation "OpenPt" => OpeningPoint (SideCtx D K Early) Msg nl w
local notation "Role" => Rounds.Role nl w

section PrefixData

variable {F Gpt X Q : Type} [Field F] [SumcheckV1Interp F]
variable [Nonempty C] {M ninp logw logc : ℕ}
local notation "Code" => ZkCode C F X Q Msg Gpt M ninp logw logc

private theorem field_ancestor_ne_opening (p : Prefix) {Resp : Type}
    (encode : Prefix → Resp → Msg) (u : Resp) {j : ℕ}
    (hj : j < (Rounds.Role.ligeroChallenge : Role).slot) :
    (Sum.inr (Sum.inl (mpoints.anc p.val j)) : Pt) ≠ openAddress encode p u := by
  intro he
  have hrole := congrArg MPoint.role (Sum.inl.inj (Sum.inr.inj he))
  have hlt := hj.trans (Rounds.Role.ligeroChallenge_lt_ligeroQuery (nl := nl) (w := w))
  have hjT : j < Rounds.Role.length nl w := hlt.trans (Rounds.Role.ligeroQuery : Role).slot_lt
  change roleAt j = .ligeroQuery at hrole
  have he' := congrArg Rounds.Role.slot hrole
  rw [slot_roleAt hjT] at he'
  exact (ne_of_lt hlt) he'

/-- Rebuild the side's system from the field ancestors preceding batch. -/
noncomputable def builtAt (V : Code) (p : Prefix) (H : Pt → C) : Option (LigeroSystem ninp M F) :=
  zkBuilt (nl := nl) (w := w) V p.val.msgFn (fun j => H (Sum.inr (Sum.inl (mpoints.anc p.val j.val))))

/-- Neither terminal answer can alter the earlier system. -/
theorem builtAt_off (V : Code) (p : Prefix) {Resp : Type}
    (encode : Prefix → Resp → Msg) (u : Resp) (H H' : Pt → C)
    (hoff : ∀ q, q ≠ batchAddress p → q ≠ openAddress encode p u → H q = H' q) :
    builtAt V p H = builtAt V p H' := by
  unfold builtAt zkBuilt
  congr 1
  apply congrArg ((zkRun (nl := nl) (w := w) V p.val.msgFn fun _ _ _ _ => ∅).state
    (Rounds.Role.layerBase w nl + 1))
  funext j
  have hj : j.val < (Rounds.Role.ligeroChallenge : Role).slot := j.isLt
  apply hoff
  · intro h
    exact mpoints.anc_ne p.val j.val (by simpa only [mpoints, p.property.1] using hj)
      (Sum.inl.inj (Sum.inr.inj h))
  · exact field_ancestor_ne_opening p encode u hj

variable (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
variable (msgH : Out → ℕ → Msg) (msgS : Out → ℕ → SigMsg)

/-- The prefix of the submitted hash proof immediately before opening. -/
noncomputable def submittedPrefix (out : Out) : Prefix :=
  parent (openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out))

/-- The submitted terminal opening is the actual side-one hash address. -/
theorem submitted_open_address (out : Out) :
    (Sum.inr (Sum.inl (openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)).val) : Pt) =
      hash2 rootH rootS avOf earlyOf msgH msgS out (1 + (Rounds.Role.ligeroQuery : Role).slot) :=
  (hash2_side1 _ _ _ _ _ _ _ (Rounds.Role.ligeroQuery : Role).slot_lt).symm

/-- The submitted batch is the actual side-one hash address. -/
theorem submitted_batch_address (out : Out) :
    (batchAddress (submittedPrefix rootH rootS avOf earlyOf msgH out) : Pt) =
      hash2 rootH rootS avOf earlyOf msgH msgS out (1 + (Rounds.Role.ligeroChallenge : Role).slot) := by
  rw [hash2_side1 _ _ _ _ _ _ _ (Rounds.Role.ligeroChallenge : Role).slot_lt]
  exact congrArg (fun p => Sum.inr (Sum.inl p)) (parent_of_submitted_opening _ _)

/-- At a submitted proof the rebuilt system is exactly `zkBuilt` on the
actual verifier field tape. -/
theorem builtAt_eq_submitted (V : Code) (out : Out) (H : Pt → C) :
    builtAt V (submittedPrefix rootH rootS avOf earlyOf msgH out) H =
      zkBuilt (nl := nl) (w := w) V (msgH out)
        (fun j => H (hash2 rootH rootS avOf earlyOf msgH msgS out (1 + j.val))) := by
  let ctx := ctxOf rootH rootS avOf earlyOf out
  let p := submittedPrefix (nl := nl) (w := w) rootH rootS avOf earlyOf msgH out
  have hp : p.val = msgPoint ctx msgH out (Rounds.Role.ligeroChallenge : Role).slot :=
    parent_of_submitted_opening _ _
  let prefixTape : Fin (Rounds.Role.length nl w) → C :=
    fun j => H (Sum.inr (Sum.inl (mpoints.anc p.val j.val)))
  change zkBuilt (nl := nl) (w := w) V p.val.msgFn prefixTape = _
  rw [zkBuilt_congr V (ms' := msgH out) (fun j hj => ?_) prefixTape]
  · unfold zkBuilt
    congr 1
    apply congrArg ((zkRun (nl := nl) (w := w) V (msgH out) fun _ _ _ _ => ∅).state
      (Rounds.Role.layerBase w nl + 1))
    funext j
    have hj : j.val < (Rounds.Role.ligeroChallenge : Role).slot := j.isLt
    change H (Sum.inr (Sum.inl (mpoints.anc p.val j.val))) =
      H (hash2 rootH rootS avOf earlyOf msgH msgS out (1 + j.val))
    rw [hp, anc_msgPoint ctx msgH out hj (Rounds.Role.ligeroChallenge : Role).slot_lt,
      hash2_side1 _ _ _ _ _ _ _ (hj.trans (Rounds.Role.ligeroChallenge : Role).slot_lt)]
  · have hslot : j < (Rounds.Role.ligeroChallenge : Role).slot := hj
    have hjT := hslot.trans (Rounds.Role.ligeroChallenge : Role).slot_lt
    rw [hp]
    simp only [MPoint.msgFn, dif_pos hjT, msgPoint, padMsgs, if_pos hslot.le]

end PrefixData

section Count

open LfzkV1.LigeroOrder125 (lowEvent badHighEvent)

variable [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
variable [Fintype K] [DecidableEq K] [Fintype Early] [DecidableEq Early]
variable [Fintype Msg] [DecidableEq Msg] [Fintype SigMsg] [DecidableEq SigMsg]
variable [Fintype C] [Nonempty C]
variable {F Gpt X Q : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable {M ninp logw logc qw nw nq nlin nt tA N TM n r : ℕ}
variable [Nonempty (SchemeTestedRow NoMask nw nq 1)]
local notation "Zk" => ZkCode C F X Q Msg Gpt M ninp logw logc
local notation "Equations" => (Fin nlin ⊕ (Fin nt × Encode.QSide))

private abbrev cert (i : Fin 4) := (OpeningGeometry125.result i).certificate
variable (i : Fin 4)
local notation "Challenge" => SchemeChallenge F NoMask nw nq 1 Equations
local notation "Openings" => QuerySet n r
local notation "Resp" => Response F r qw n 1
local notation "Code" => MultiplicativeCode F r qw n
local notation "Oracle" => Ligero.V1.Oracle F nw nq n 1

/-- Low and bad-high terminal acceptance on the actual two-field search
costs the batch and opening role budgets. The representation premises
ensure that a wire response has one raw encoding at each prefix. -/
theorem count_le {Wire : Type} [Fintype Wire]
    (hn : n = (cert i).n) (hr : r = (cert i).openings) (code : Code)
    (body : TwoOracleTree Enc D Pt C Out tA N)
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (msgH : Out → ℕ → Msg) (msgS : Out → ℕ → SigMsg)
    (mt : Fin TM → D)
    (VAt : Cut D Enc → Prefix → Zk) (oracleOf : Cut D Enc → Oracle)
    (pl : Encode.Placement ninp M qw nw nq nt)
    (toResponse : Wire ↪ Resp) (wireResponse : Out → Wire) (encode : Prefix → Wire → Msg)
    (decode : Prefix → Msg → Option Wire) (valid : Prefix → Msg → Prop)
    (hdecode : ∀ p u, decode p (encode p u) = some u)
    (hvalid : ∀ p m u, valid p m → decode p m = some u → encode p u = m)
    (decodeBatch : Prefix → ExactDecoder C Challenge) (decodeOpen : Prefix → ExactDecoder C Openings)
    (hfield : Fintype.card F = (cert i).fieldSize) (hk : code.k = (cert i).k)
    (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
    (hRS : JBAgreement.RSPresentation n (cert i).k code.baseCode)
    (event : (Pt → C) → Prop)
    (hwire : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let o : OpenPt := openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
        let m := o.val.msgs openingIndex
        valid (parent o) m ∧ decode (parent o) m = some (wireResponse out))
    (hpass : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let κ := S.context mt H
        let p : Prefix := submittedPrefix rootH rootS avOf earlyOf msgH out
        let tape : Fin (Rounds.Role.length nl w) → C := fun j => H (S.hashInput out (1 + j.val))
        let ch := (decodeBatch p).decode (tape (Rounds.Role.ligeroChallenge : Role).index)
        let q := (decodeOpen p).decode (tape (Rounds.Role.ligeroQuery : Role).index)
        ∃ sys, zkBuilt (nl := nl) (w := w) (VAt κ p) (msgH out) tape = some sys ∧
          let s := (oracleOf κ, ZkLigeroV1.stmtOf pl nlin sys)
          lowEvent i code s (toResponse (wireResponse out)) ch q ∨
            badHighEvent i code s (toResponse (wireResponse out)) ch q) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ ∑ H : Pt → C,
      ((319 / (100 * 2 ^ 128) : ℚ) * (observedRole (S.search mt) .batch H).card +
        (3188 / (500 * 2 ^ 128) : ℚ) * ((observedRole (S.search mt) .opening H).card + 1)) := by
  classical
  subst n
  subst r
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  let batch (p : Prefix) : Pt := batchAddress p
  let opening (p : Prefix) (u : Wire) : Pt := openAddress encode p u
  let cut (p : Prefix) (H : Pt → C) := (S.atOracle H).ctxAt mt Setup.emptyTape (S.key (batch p))
  let context (p : Prefix) (H : Pt → C) :=
    let κ := cut p H
    (oracleOf κ, ZkLigeroV1.stmtOf pl nlin ((builtAt (VAt κ p) p H).getD emptySys))
  let selected (out : Out) : Prefix × Wire :=
    (submittedPrefix rootH rootS avOf earlyOf msgH out, wireResponse out)
  have hne (p : Prefix) (u : Wire) : batch p ≠ opening p u := batch_open_ne encode p p u
  have hoff (p : Prefix) (u : Wire) (H H' : Pt → C)
      (h : ∀ q, q ≠ batch p → q ≠ opening p u → H q = H' q) : context p H = context p H' := by
    have hkeys : S.key (batch p) = S.key (opening p u) :=
      batch_open_same_key (SigMsg := SigMsg) (nlS := nlS) (widthsS := wS) encode p u
    have hcut : cut p H = cut p H' := ctxAt_off_pair S mt H H' (batch p) (opening p u)
      hkeys.symm h
    dsimp only [context]
    rw [hcut, builtAt_off (VAt (cut p H') p) p encode u H H' h]
  have hb : Function.Injective batch := batchAddress_injective
  have ho : Function.Injective (fun pu : Prefix × Wire => opening pu.1 pu.2) :=
    openAddress_injective encode decode hdecode
  have hbRole (p : Prefix) : queryRole (batch p) = .batch := by
    change (match p.val.role with
      | .ligeroChallenge => QueryRole.batch
      | .ligeroQuery => QueryRole.opening
      | _ => QueryRole.field) = .batch
    rw [p.property.1]
  have hoRole (p : Prefix) (u : Wire) : queryRole (opening p u) = .opening := rfl
  have hcharge := LigeroOrder125.v7_ordered_charge_le i code toResponse (S.search mt) selected batch opening
    hne context hoff decodeBatch decodeOpen hfield hk hmin hRS
  let counted (H : Pt → C) :=
    let j := selected ((S.search mt).run H).1
    let a := (decodeBatch j.1).decode (H (batch j.1))
    let b := (decodeOpen j.1).decode (H (opening j.1 j.2))
    lowEvent i code (context j.1 H) (toResponse j.2) a b ∨
      badHighEvent i code (context j.1 H) (toResponse j.2) a b
  have hcover : ∀ H, event H → counted H := by
    intro H he
    let out := S.proof mt H
    let o : OpenPt := openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
    let p : Prefix := parent o
    have hbAt : batch p = S.hashInput out (1 + (Rounds.Role.ligeroChallenge : Role).slot) :=
      submitted_batch_address rootH rootS avOf earlyOf msgH msgS out
    have hoAt : opening p (wireResponse out) = S.hashInput out (1 + (Rounds.Role.ligeroQuery : Role).slot) := by
      have hwire' := hwire H he
      have heq : openAt encode p (wireResponse out) = o :=
        openAt_eq_of_valid encode decode valid hvalid o (wireResponse out) hwire'.1 hwire'.2
      change (Sum.inr (Sum.inl (openAt encode p (wireResponse out)).val) : Pt) = _
      rw [heq]
      exact submitted_open_address rootH rootS avOf earlyOf msgH msgS out
    have hc : cut p H = S.context mt H := by
      unfold cut
      rw [hbAt, S.hkey out]
      rfl
    obtain ⟨sys, hbuilt, hbad⟩ := hpass H he
    have hcontext : context p H = (oracleOf (S.context mt H), ZkLigeroV1.stmtOf pl nlin sys) := by
      have hB := builtAt_eq_submitted rootH rootS avOf earlyOf msgH msgS (VAt (S.context mt H) p) out H
      change builtAt (VAt (S.context mt H) p) p H =
        zkBuilt (nl := nl) (w := w) (VAt (S.context mt H) p) (msgH out)
          (fun j => H (S.hashInput out (1 + j.val))) at hB
      change zkBuilt (nl := nl) (w := w) (VAt (S.context mt H) p) (msgH out)
        (fun j => H (S.hashInput out (1 + j.val))) = some sys at hbuilt
      dsimp only [context]
      rw [hc, hB, hbuilt]
      rfl
    unfold counted
    rw [← S.proof_eq mt H]
    change lowEvent i code (context p H) (toResponse (wireResponse out))
      ((decodeBatch p).decode (H (batch p))) ((decodeOpen p).decode (H (opening p (wireResponse out)))) ∨
      badHighEvent i code (context p H) (toResponse (wireResponse out))
        ((decodeBatch p).decode (H (batch p))) ((decodeOpen p).decode (H (opening p (wireResponse out))))
    rw [hcontext, hbAt, hoAt]
    exact hbad
  calc
    _ ≤ ∑ H : Pt → C, LigeroOrder125.indicator (counted H) := by
      rw [card_filter, Nat.cast_sum]
      apply sum_le_sum
      intro H _
      by_cases he : event H
      · simp only [if_pos he, Nat.cast_one, LigeroOrder125.indicator, if_pos (hcover H he), le_refl]
      · simp only [if_neg he, Nat.cast_zero, LigeroOrder125.indicator]
        split_ifs <;> norm_num
    _ ≤ _ := hcharge.trans (sum_le_sum (fun H _ => by
      have hB := batch_count_le_observed (S.search mt) H batch hb hbRole
      have hO := opening_counts_le_observed (S.search mt) H batch opening ho hoRole
      have hA := LigeroOrder125.appended_count_le (S.search mt) selected opening H
      have hLate : 0 ≤ LigeroOrder125.lateCount (S.search mt) batch opening H := by
        apply sum_nonneg
        intro a _
        unfold LigeroOrder125.indicator
        split_ifs <;> norm_num
      linarith))

open LfzkV1.LiftOpening125 in
/-- Ambiguity is paid at the submitted opening. Its witnesses are fixed by
the cut for that address, including for an arbitrary raw opening message. -/
theorem ambiguity_count_le (hn : n = (cert i).n) (hr : r = (cert i).openings) (code : Code)
    (body : TwoOracleTree Enc D Pt C Out tA N)
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (msgH : Out → ℕ → Msg) (msgS : Out → ℕ → SigMsg)
    (mt : Fin TM → D) (oracleOf : Cut D Enc → Oracle)
    (decodeOpen : Pt → ExactDecoder C Openings)
    (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
    (hcard : ∀ κ, Fintype.card (SchemeLiftCandidate code (oracleOf κ) (HashCut125.radius i)) ≤ 2)
    (event : (Pt → C) → Prop)
    (hcover : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let p := S.hashInput out (1 + (Rounds.Role.ligeroQuery : Role).slot)
        let b := (decodeOpen p).decode (H p)
        ∃ x y : SchemeLiftCandidate code (oracleOf (S.context mt H)) (HashCut125.radius i),
          x ≠ y ∧ Compatible x b (cert i).g ∧ Compatible y b (cert i).g) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ ∑ H : Pt → C,
      ((1 / 2 ^ 202 : ℚ) * ((observedRole (S.search mt) .opening H).card + 1)) := by
  subst n
  subst r
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  let opening (out : Out) : Pt :=
    Sum.inr (Sum.inl (openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)).val)
  let cut (p : Pt) (H : Pt → C) := (S.atOracle H).ctxAt mt Setup.emptyTape (S.key p)
  let bad (p : Pt) (H : Pt → C) (a : C) :=
    let b := (decodeOpen p).decode a
    ∃ x y : SchemeLiftCandidate code (oracleOf (cut p H)) (HashCut125.radius i),
      x ≠ y ∧ Compatible x b (cert i).g ∧ Compatible y b (cert i).g
  have hbRole (out : Out) : queryRole (opening out) = .opening := by
    let o : OpenPt := openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
    change (match o.val.role with
      | .ligeroChallenge => QueryRole.batch
      | .ligeroQuery => QueryRole.opening
      | _ => QueryRole.field) = .opening
    rw [o.property]
  have hoff (p : Pt) (H H' : Pt → C) (h : AgreeOff p H H') (a : C) :
      bad p H a ↔ bad p H' a := by
    have hc : cut p H = cut p H' := (S.ctxAt_off mt H H' p h).symm
    dsimp only [bad]
    rw [hc]
  have hfiber (p : Pt) (H : Pt → C) :
      (∑ a : C, @ite ℚ (bad p H a) (Classical.propDecidable _) 1 0) ≤ Fintype.card C * (1 / 2 ^ 202) := by
    let d : @ExactDecoder C (QuerySet (cert i).n (cert i).openings) _ _
        (fun a b => Classical.propDecidable (a = b)) := by
      refine @ExactDecoder.mk C (QuerySet (cert i).n (cert i).openings) _ _
        (fun a b => Classical.propDecidable (a = b))
        (decodeOpen p).decode (decodeOpen p).k ?_ (decodeOpen p).hexact
      intro b
      rw [Finset.filter_congr_decidable (univ : Finset C) (fun a => (decodeOpen p).decode a = b)
        (fun _ => Classical.propDecidable _)]
      exact (decodeOpen p).hbal b
    have h := HashOpening125.ambiguous_decoded_le (C := code) (oracle := oracleOf (cut p H))
      i d hmin (hcard (cut p H))
    convert h using 1
    apply sum_congr rfl
    intro a _
    exact @ite_congr ℚ _ _ _ _ _ _ (Classical.propDecidable _) (Classical.propDecidable _)
      rfl (fun _ => rfl) (fun _ => rfl)
  have hfinal (H : Pt → C) (he : event H) :
      let p := opening ((S.search mt).run H).1; bad p H (H p) := by
    let out := S.proof mt H
    have hp : opening out = S.hashInput out (1 + (Rounds.Role.ligeroQuery : Role).slot) :=
      submitted_open_address rootH rootS avOf earlyOf msgH msgS out
    have hc : cut (opening out) H = S.context mt H := by
      unfold cut
      rw [hp, S.hkey out]
      rfl
    dsimp only
    rw [← S.proof_eq mt H]
    change bad (opening out) H (H (opening out))
    dsimp only [bad]
    rw [hc, hp]
    exact hcover H he
  have h := MacCharge125.selected_role_event_count_le (S.search mt)
    (fun p => queryRole p = .opening) opening hbRole bad hoff (1 / 2 ^ 202) hfiber event hfinal
  refine h.trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro H _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (MacCharge125.appendedKeyCount_le_one (S.search mt) opening H)

end Count

section Compiled

open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit Merkle.MH

variable [Fintype C] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable {F X Salt : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable [Inhabited Salt] {M nt nlin : ℕ} {i : Fin 4}
variable {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey)

/-- Exactly balanced batching decoder from the registered hash-side code. -/
def batchDecoder (a : C) (x : X) :
    ExactDecoder C (ZkLigeroV1.Chal F (v7HashRow i).params.nw (v7HashRow i).params.nq nlin nt) where
  decode := (side.Vc a x).decodeChal
  k := side.kchal
  hbal := side.hbalChal a x
  hexact := side.hkchal

/-- Exactly balanced opening decoder from the registered hash-side code. -/
def openingDecoder (a : C) (x : X) :
    ExactDecoder C (LigeroV1LayerStep.Qry (v7HashRow i).params.row) where
  decode := (side.Vc a x).decodeQuery
  k := side.kq
  hbal := side.hbalQuery a x
  hexact := side.hkq

/-- The registered code has the geometry used in the terminal bounds. -/
theorem code_facts (hF : Fintype.card F = 2 ^ 128) :
    let R := v7HashRow i
    let code := R.params.row.code (Row.rowValid hR) side.dom (Row.hkrow hR)
    R.params.row.n = (cert i).n ∧ R.params.row.openings = (cert i).openings ∧
      Fintype.card F = (cert i).fieldSize ∧ code.k = (cert i).k ∧
      HasMinimumDistanceAtLeast code.baseCode (cert i).d ∧
      Nonempty (JBAgreement.RSPresentation R.params.row.n (cert i).k code.baseCode) := by
  obtain ⟨hn, hk, hr', hf⟩ := OpeningGeometry125.deployedGeometry i
  obtain ⟨hcodek, _, hRS⟩ := (v7HashRow i).params.row.rsFacts (Row.rowValid hR) side.dom (Row.hkrow hR)
  change (cert i).k = (v7HashRow i).params.row.k at hk
  refine ⟨hn.symm, hr'.symm, hF.trans hf.symm, hcodek.trans hk.symm,
    HashCircuitReplay125.code_distance side, ?_⟩
  rw [hk]
  exact hRS

section Deployed

open LfzkV1.CompiledLongfellow (ligIdx qryIdx)
open LfzkV1.CompiledLongfellowAdaptive (slice1)

variable [Fintype D] [Fintype K] [DecidableEq K] [Fintype Early] [DecidableEq Early]
variable [Fintype Msg] [DecidableEq Msg] [Fintype SigMsg] [DecidableEq SigMsg] [Nonempty C]
variable {tA N TM : ℕ}

set_option quotPrecheck false
local notation "R" => v7HashRow i
local notation "HashPrefix" => BatchPrefix (SideCtx D K Early) Msg (R).params.nl (R).params.rounds
local notation "HashOpening" => OpeningPoint (SideCtx D K Early) Msg (R).params.nl (R).params.rounds
local notation "V7Point" => SignatureBudget125.PairPoint D K Early Msg SigMsg R
local notation "ActualResponse" => Response F (R).params.row.openings (R).params.q (R).params.row.n 1

private theorem tested_rows (j : Fin 4) :
    Nonempty (SchemeTestedRow NoMask (v7HashRow j).params.nw (v7HashRow j).params.nq 1) :=
  schemeTestedRowNonemptyOfCoreRows (Or.inl (by fin_cases j <;> decide +kernel))

/-- The ordered count on the actual registered hash circuit. The event
uses the selected proof's built system and its direct terminal exception.
Only the wire response has an encoding round trip. -/
theorem compiled_count_le {Wire : Type} [Fintype Wire]
    (body : TwoOracleTree Enc D V7Point C Out tA N)
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (represent : K → C) (pubAt : Early → X)
    (msgH : Out → ℕ → Msg) (msgS : Out → ℕ → SigMsg)
    (mt : Fin TM → D) (hF : Fintype.card F = 2 ^ 128)
    (toResponse : Wire ↪ ActualResponse) (wireResponse : Out → Wire)
    (encode : HashPrefix → Wire → Msg)
    (decode : HashPrefix → Msg → Option Wire) (valid : HashPrefix → Msg → Prop)
    (hdecode : ∀ p u, decode p (encode p u) = some u)
    (hvalid : ∀ p m u, valid p m → decode p m = some u → encode p u = m)
    (event : (V7Point → C) → Prop)
    (hwire : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let o : HashOpening := openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
        let m := o.val.msgs openingIndex
        valid (parent o) m ∧ decode (parent o) m = some (wireResponse out) ∧
          toResponse (wireResponse out) = side.respOf m)
    (hpass : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let V := side.Vc (represent (avOf out)) (pubAt (earlyOf out))
        let tape := slice1 R v7SigHahn (S.challenges mt H)
        let κ := S.context mt H
        let cut := extOracle nlin nt (Row.rowValid hR) side.dom (Row.hkrow hR) hr dec
          (rootOfKey κ.1, κ.2)
        let code := (R).params.row.code (Row.rowValid hR) side.dom (Row.hkrow hR)
        ∃ sys, zkBuilt V (msgH out) tape = some sys ∧
          HashCircuitReplay125.directTerminal i code cut (ZkLigeroV1.stmtOf side.pl nlin sys)
            (V.decodeChal (tape ligIdx)) (side.respOf (msgH out (Rounds.Role.ligeroQuery :
              Rounds.Role (R).params.nl (R).params.rounds).slot)) (V.decodeQuery (tape qryIdx))) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ ∑ H : V7Point → C,
      ((319 / (100 * 2 ^ 128) : ℚ) * (observedRole (S.search mt) .batch H).card +
        (3188 / (500 * 2 ^ 128) : ℚ) * ((observedRole (S.search mt) .opening H).card + 1)) := by
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  let code := (R).params.row.code (Row.rowValid hR) side.dom (Row.hkrow hR)
  let oracleOf (κ : Cut D Enc) := extOracle nlin nt (Row.rowValid hR) side.dom (Row.hkrow hR) hr dec
    (rootOfKey κ.1, κ.2)
  let VAt (_ : Cut D Enc) (p : HashPrefix) := side.Vc (represent p.val.ctx.2.1) (pubAt p.val.ctx.2.2)
  let batchD (p : HashPrefix) := batchDecoder side (represent p.val.ctx.2.1) (pubAt p.val.ctx.2.2)
  let openD (p : HashPrefix) := openingDecoder side (represent p.val.ctx.2.1) (pubAt p.val.ctx.2.2)
  letI := tested_rows i
  obtain ⟨hn, hr', hfield, hk, hmin, ⟨hRS⟩⟩ := code_facts side hF
  refine count_le i hn hr' code body rootH rootS avOf earlyOf msgH msgS mt VAt oracleOf side.pl
    toResponse wireResponse encode decode valid hdecode hvalid batchD openD hfield hk hmin hRS event ?_ ?_
  · intro _ H he
    have h := hwire H he
    exact ⟨h.1, h.2.1⟩
  · intro _ H he
    let out := S.proof mt H
    let o : HashOpening := openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
    have hm : o.val.msgs openingIndex = msgH out (Rounds.Role.ligeroQuery :
        Rounds.Role (R).params.nl (R).params.rounds).slot := by
      let j := (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot
      change (if j ≤ j then msgH out j else default) = msgH out j
      simp only [le_refl, if_true]
    have hreal : toResponse (wireResponse out) = side.respOf (msgH out (Rounds.Role.ligeroQuery :
        Rounds.Role (R).params.nl (R).params.rounds).slot) :=
      (hwire H he).2.2.trans (congrArg side.respOf hm)
    obtain ⟨sys, hBuilt, hterm⟩ := hpass H he
    refine ⟨sys, hBuilt, ?_⟩
    dsimp only
    rw [hreal]
    exact (HashCircuitReplay125.directTerminal_iff_ordered ..).mp hterm

open LfzkV1.LiftOpening125 in
/-- Charge ambiguity to the opening role of the registered hash circuit. -/
theorem compiled_ambiguity_count_le [Nonempty X]
    (body : TwoOracleTree Enc D V7Point C Out tA N)
    (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
    (represent : K → C) (pubAt : Early → X)
    (msgH : Out → ℕ → Msg) (msgS : Out → ℕ → SigMsg)
    (mt : Fin TM → D) (event : (V7Point → C) → Prop)
    (hcover : let S := setup2 body rootH rootS avOf earlyOf msgH msgS
      ∀ H, event H →
        let out := S.proof mt H
        let a := represent (avOf out)
        let x := pubAt (earlyOf out)
        let κ := S.context mt H
        let query := (side.Vc a x).decodeQuery (slice1 R v7SigHahn (S.challenges mt H) qryIdx)
        ∃ u v : sideLiftAt side (HashCut125.radius i) (κ, a, x),
          u ≠ v ∧ Compatible u query (cert i).g ∧ Compatible v query (cert i).g) :
    let S := setup2 body rootH rootS avOf earlyOf msgH msgS
    ((univ.filter event).card : ℚ) ≤ ∑ H : V7Point → C,
      ((1 / 2 ^ 202 : ℚ) * ((observedRole (S.search mt) .opening H).card + 1)) := by
  let S := setup2 body rootH rootS avOf earlyOf msgH msgS
  let code := (R).params.row.code (Row.rowValid hR) side.dom (Row.hkrow hR)
  let oracleOf (κ : Cut D Enc) := extOracle nlin nt (Row.rowValid hR) side.dom (Row.hkrow hR) hr dec
    (rootOfKey κ.1, κ.2)
  let a₀ := Classical.arbitrary C
  let x₀ := Classical.arbitrary X
  let openD (p : V7Point) := match p with
    | Sum.inr (Sum.inl q) => openingDecoder side (represent q.ctx.2.1) (pubAt q.ctx.2.2)
    | _ => openingDecoder side a₀ x₀
  obtain ⟨hn, _, hr', _⟩ := OpeningGeometry125.deployedGeometry i
  letI := tested_rows i
  have hcard (κ : Cut D Enc) : Fintype.card (SchemeLiftCandidate code (oracleOf κ) (HashCut125.radius i)) ≤ 2 :=
    (HashCut125.side_lift_card_le side (κ, a₀, x₀)).trans_eq (HashCut125.row_candidate_count i)
  refine ambiguity_count_le i hn.symm hr'.symm code body rootH rootS avOf earlyOf msgH msgS mt
    oracleOf openD (HashCircuitReplay125.code_distance side) hcard event ?_
  intro _ H he
  let out := S.proof mt H
  let j := (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot
  let p := S.hashInput out (1 + j)
  have hj : j < Rounds.Role.length (R).params.nl (R).params.rounds :=
    (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot_lt
  have hp : p = (Sum.inr (Sum.inl (msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out j)) : V7Point) :=
    hash2_side1 rootH rootS avOf earlyOf msgH msgS out hj
  have hdecode : (openD p).decode = (side.Vc (represent (avOf out)) (pubAt (earlyOf out))).decodeQuery := by
    rw [hp]
    rfl
  change ∃ u v : SchemeLiftCandidate code (oracleOf (S.context mt H)) (HashCut125.radius i),
    u ≠ v ∧ Compatible u ((openD p).decode (H p)) (cert i).g ∧
      Compatible v ((openD p).decode (H p)) (cert i).g
  rw [hdecode]
  exact hcover H he

end Deployed

end Compiled

end LfzkV1.TerminalCharge125
