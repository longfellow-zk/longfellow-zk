import LfzkV1.HashFieldProfile125
import LfzkV1.HashOpening125
import LfzkV1.NizkDeployedHashTwoField
import LfzkV1.TwoFieldCover125

/-! Ordered charges for the canonical secondary lift on actual hash points. -/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000

namespace LfzkV1.HashCanonicalCharge125

open Finset LigeroFamily CodingTheory Merkle.MH Merkle.RandomOracle
open Bcs.TotalOracle Bcs.TotalOracleCommit
open LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit LfzkV1.Arith LfzkV1.ZkArithProfile
open LfzkV1.CompiledZk LfzkV1.RbrZkLongfellow RbrLongfellow
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField
open LfzkV1.TwoFieldV1Rows (ExactDecoder)
open scoped Classical

private abbrev cert (j : Fin 4) := (OpeningGeometry125.result j).certificate

section Transport

open LfzkV1.LigeroHighMass125 (liftedResponses highCutoff)
attribute [local instance 10000] Classical.propDecidable

variable {A F E : Type} [Fintype A] [Field F] [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E] {n r w nw nq : ℕ}
variable (i : Fin 4) (hn : n = (cert i).n) (hr : r = (cert i).openings)
variable {code : MultiplicativeCode F r w n} {oracle : Ligero.V1.Oracle F nw nq n 1}
variable (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
variable (lift : SchemeLiftCandidate code oracle (HashCut125.radius i))
variable (hsec : LiftOpening125.primary code oracle (HashCut125.radius i) ≠ some lift)

omit [Fintype E] [DecidableEq E] in
include hn hr hmin hsec in
private theorem compatible_at_geometry (dec : ExactDecoder A (QuerySet n r)) :
    (∑ coin : A, if LiftOpening125.Compatible lift (dec.decode coin) (cert i).g
      then (1 : ℚ) else 0) ≤ Fintype.card A * (1 / 2 ^ 32) := by
  subst n
  subst r
  exact HashOpening125.secondaryCompatible_decoded_le (C := code) (oracle := oracle)
    i dec hmin lift hsec

include hn hr hmin hsec in
private theorem response_unique_at_geometry (hk : code.k = (cert i).k)
    (statement : ConstraintSystem F nw nq w E)
    (batch : SchemeChallenge F NoMask nw nq 1 E)
    {a b : Response F r w n 1}
    (ha : a ∈ liftedResponses statement lift (highCutoff i) (cert i).g batch)
    (hb : b ∈ liftedResponses statement lift (highCutoff i) (cert i).g batch) : a = b := by
  subst n
  subst r
  exact HashOpening125.secondaryResponse_unique (C := code) (oracle := oracle)
    i statement hmin hk lift hsec ha hb

include hn hr hmin hsec in
private theorem response_opening_at_geometry (dec : ExactDecoder A (QuerySet n r))
    (statement : ConstraintSystem F nw nq w E)
    (batch : SchemeChallenge F NoMask nw nq 1 E)
    (response : Response F r w n 1)
    (ha : response ∈ liftedResponses statement lift (highCutoff i) (cert i).g batch) :
    (∑ coin : A, if SchemeVerifier.Accepts code Ligero.V1.scheme statement batch response
      (dec.decode coin) (openSchemeOracle oracle (dec.decode coin)) then (1 : ℚ) else 0) ≤
        Fintype.card A * (1 / 2 ^ 108) := by
  subst n
  subst r
  exact HashOpening125.secondaryResponse_decoded_le (C := code) (oracle := oracle)
    i statement dec hmin lift hsec ha

end Transport

section Density

variable {C D Enc X Msg Salt F : Type} [Fintype C]
  [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
  {M nt nlin : ℕ} {i : Fin 4} {hR : (v7HashRow i).Valid}
  {hr : 0 < (v7HashRow i).params.row.openings}
  {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
  {dec : RoleDecoders codec}
variable (Side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec Prod.fst)

local notation "RowV7" => v7HashRow i
local notation "Lift" => sideLiftAt Side (HashCut125.radius i)
local notation "Query" => LigeroV1LayerStep.Qry (v7HashRow i).params.row

private noncomputable abbrev codeOf :=
  (v7HashRow i).params.row.code (Row.rowValid hR) Side.dom (Row.hkrow hR)

private noncomputable abbrev oracleOf (σ : Sig D C X Enc) :=
  extOracle nlin nt (Row.rowValid hR) Side.dom (Row.hkrow hR) hr dec (σ.1.1.1, σ.1.2)

private theorem distance (Side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i)
    C F Msg M nt nlin X dec Prod.fst) :
    HasMinimumDistanceAtLeast (codeOf Side).baseCode (cert i).d := by
  have hd : (cert i).d = (v7HashRow i).params.row.n -
      ((v7HashRow i).params.row.openings + (v7HashRow i).params.q) + 1 := by fin_cases i <;> rfl
  have hn : (v7HashRow i).params.row.openings + (v7HashRow i).params.q ≤
      (v7HashRow i).params.row.n := by fin_cases i <;> decide
  rw [hd]
  exact ReedSolomon.baseCode_minimum_distance Side.dom (by omega) hn

/-- The opening decode registered by the compiled hash side. -/
abbrev decodeQuery (σ : Sig D C X Enc) := (Side.Vc σ.2.1 σ.2.2).decodeQuery

private noncomputable def queryDecoder (σ : Sig D C X Enc) :
    @ExactDecoder C Query _ _ (fun a b => Classical.propDecidable (a = b)) := by
  refine @ExactDecoder.mk C Query _ _ (fun a b => Classical.propDecidable (a = b))
    (Side.Vc σ.2.1 σ.2.2).decodeQuery Side.kq ?_ Side.hkq
  intro q
  rw [Finset.filter_congr_decidable (univ : Finset C)
    (fun a => (Side.Vc σ.2.1 σ.2.2).decodeQuery a = q) (fun _ => Classical.propDecidable _)]
  exact Side.hbalQuery σ.2.1 σ.2.2 q

/-- Compatibility of the raw opening answer with the secondary lift. This
event reads the commitment cut and the supplied coin. -/
def compatible (σ : Sig D C X Enc) (coin : C) : Prop :=
  ∃ lift : Lift σ, HashFieldProfile125.primary Side σ ≠ some lift ∧
    LiftOpening125.Compatible lift (decodeQuery Side σ coin) (cert i).g

private theorem compatible_lift_sum_le (σ : Sig D C X Enc) (lift : Lift σ)
    (hsec : HashFieldProfile125.primary Side σ ≠ some lift) :
    (∑ coin : C, @ite ℚ (LiftOpening125.Compatible lift (decodeQuery Side σ coin)
      (cert i).g) (Classical.propDecidable _) 1 0) ≤ Fintype.card C * (1 / 2 ^ 32) := by
  have hg := OpeningGeometry125.deployedGeometry i
  exact compatible_at_geometry i hg.1.symm hg.2.2.1.symm
    (code := codeOf Side) (oracle := oracleOf Side σ) (distance Side) lift hsec
    (queryDecoder Side σ)

/-- The secondary compatibility bound on raw v1 opening answers. -/
theorem compatible_sum_le (σ : Sig D C X Enc) :
    (∑ coin : C, if compatible Side σ coin then (1 : ℚ) else 0) ≤
      Fintype.card C * (1 / 2 ^ 32) := by
  by_cases hs : ∃ lift : Lift σ, HashFieldProfile125.primary Side σ ≠ some lift
  · obtain ⟨lift, hl⟩ := hs
    have heq (coin : C) : compatible Side σ coin ↔
        LiftOpening125.Compatible lift (decodeQuery Side σ coin) (cert i).g := by
      constructor
      · rintro ⟨other, ho, hgood⟩
        obtain rfl := HashFieldProfile125.secondary_unique Side σ other lift ho hl
        exact hgood
      · exact fun h => ⟨lift, hl, h⟩
    refine (Finset.sum_le_sum fun coin _ => ?_).trans (compatible_lift_sum_le Side σ lift hl)
    by_cases hc : compatible Side σ coin
    · rw [if_pos hc, if_pos ((heq coin).1 hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((heq coin).2 h))]
  · have heq (coin : C) : ¬ compatible Side σ coin :=
      fun ⟨lift, hl, _⟩ => hs ⟨lift, hl⟩
    simp only [heq, if_false, Finset.sum_const_zero]
    positivity

open LfzkV1.ZkLigeroV1 (Chal)
open LfzkV1.LigeroHighMass125 (liftedResponses highCutoff)

local notation "Batch" => Chal F (v7HashRow i).params.nw (v7HashRow i).params.nq nlin nt

/-- The V1 verifier checks the fixed response against the decoded opening at
the same frozen tableau. -/
def decodedAccepts (σ : Sig D C X Enc) (sys : LigeroSystem Side.c.ninp M F)
    (batch : Batch) (msg : Msg) (coin : C) : Prop :=
  let query := decodeQuery Side σ coin
  SchemeVerifier.Accepts (codeOf Side) Ligero.V1.scheme
    (Encode.encodeLig Side.pl nlin sys) batch (Side.respOf msg) query
    (openSchemeOracle (oracleOf Side σ) query)

/-- A response is eligible for the canonical secondary lift if it reaches
the high-agreement threshold and is supported by that lift's puncturing. -/
def highReply (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((HashCut125.side Side).V σ)
      (v7HashRow i).params.nl (v7HashRow i).params.rounds)
    (lift : Lift σ) (built : Option (LigeroSystem Side.c.ninp M F))
    (batch : Batch) (msg : Msg) : Prop :=
  ∃ sys, built = some sys ∧ wire.valid .ligeroQuery msg ∧
    Side.respOf msg ∈ liftedResponses (Encode.encodeLig Side.pl nlin sys)
      lift (highCutoff i) (cert i).g batch

private theorem code_k : (codeOf Side).k = (cert i).k := by
  have hk := Row.hkrow hR
  change (v7HashRow i).params.row.openings + (v7HashRow i).params.q = (cert i).k
  rw [hk]
  fin_cases i <;> rfl

theorem highReply_unique (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((HashCut125.side Side).V σ)
      (v7HashRow i).params.nl (v7HashRow i).params.rounds)
    (hencoding : ∀ {a b}, wire.valid .ligeroQuery a → wire.valid .ligeroQuery b →
      Side.respOf a = Side.respOf b → a = b)
    (lift : Lift σ) (hsec : HashFieldProfile125.primary Side σ ≠ some lift)
    (built : Option (LigeroSystem Side.c.ninp M F)) (batch : Batch) {a b : Msg}
    (ha : highReply Side σ wire lift built batch a)
    (hb : highReply Side σ wire lift built batch b) : a = b := by
  obtain ⟨sys, rfl, hva, ha⟩ := ha
  obtain ⟨sys', he, hvb, hb⟩ := hb
  obtain rfl := Option.some.inj he
  apply hencoding hva hvb
  have hg := OpeningGeometry125.deployedGeometry i
  exact response_unique_at_geometry i hg.1.symm hg.2.2.1.symm
    (code := codeOf Side) (oracle := oracleOf Side σ) (distance Side) lift hsec
    (code_k Side) _ _ ha hb

theorem decodedAccepts_sum_le (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((HashCut125.side Side).V σ)
      (v7HashRow i).params.nl (v7HashRow i).params.rounds)
    (lift : Lift σ) (hsec : HashFieldProfile125.primary Side σ ≠ some lift)
    (sys : LigeroSystem Side.c.ninp M F) (batch : Batch) (msg : Msg)
    (hhigh : highReply Side σ wire lift (some sys) batch msg) :
    (∑ coin : C, @ite ℚ (decodedAccepts Side σ sys batch msg coin) (Classical.propDecidable _) 1 0) ≤
      Fintype.card C * (1 / 2 ^ 108) := by
  obtain ⟨sys', he, _, hhigh⟩ := hhigh
  obtain rfl := Option.some.inj he
  have hg := OpeningGeometry125.deployedGeometry i
  exact response_opening_at_geometry i hg.1.symm hg.2.2.1.symm
    (code := codeOf Side) (oracle := oracleOf Side σ) (distance Side) lift hsec
    (queryDecoder Side σ) _ _ _ hhigh

end Density


section Search

variable {C D K Enc Early X MsgH MsgS Out Salt F : Type}
  [Fintype C] [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
  [Inhabited MsgH] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS]
  {M nt nlin tA N L TM nlS : ℕ} {wS : ℕ → ℕ}
  {i : Fin 4} {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
  {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
  {dec : RoleDecoders codec}

local notation "HPoint" => MPoint (SideCtx D K Early) MsgH
  (v7HashRow i).params.nl (v7HashRow i).params.rounds
local notation "Point" => Pt2 D K Early MsgH MsgS
  (v7HashRow i).params.nl nlS (v7HashRow i).params.rounds wS
local notation "Init" => CanonicalSecondary125.InitPoint (SideCtx D K Early) MsgH
  (v7HashRow i).params.nl (v7HashRow i).params.rounds

variable (Side : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F MsgH M nt nlin X dec Prod.fst)
local notation "Lift" => sideLiftAt Side (HashCut125.radius i)
variable (S : Setup Enc D (Pt2 D K Early MsgH MsgS (v7HashRow i).params.nl nlS
  (v7HashRow i).params.rounds wS) C Out (D × D) tA N L) (mt : Fin TM → D)
variable (represent : K → C) (publicOf : Early → X)

def address (p : HPoint) : Point := .inr (.inl p)

private def sigAt (p : HPoint) (cut : (D × D) × List (Enc × D)) : Sig D C X Enc :=
  (cut, represent p.ctx.2.1, publicOf p.ctx.2.2)

/-- The same commitment cut used by the adaptive verifier, addressed by key. -/
noncomputable def cutAt (H : Point → C) (key : D × D) : (D × D) × List (Enc × D) :=
  (S.atOracle H).ctxAt mt Setup.emptyTape key

omit [Fintype C] [Inhabited MsgH] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem cutAt_off (p : Point) (H H' : Point → C) (hoff : AgreeOff p H H') :
    cutAt S mt H (S.key p) = cutAt S mt H' (S.key p) :=
  (S.ctxAt_off mt H H' p hoff).symm

local notation "OpeningAddress" => CanonicalSecondary125.OpeningPoint (SideCtx D K Early) MsgH
  (v7HashRow i).params.nl (v7HashRow i).params.rounds

noncomputable def earlyParent (p : OpeningAddress) : Point :=
  address (CanonicalSecondary125.initialOf p).val

def earlyChild (p : OpeningAddress) : Point := address p.val

omit [Inhabited D] [DecidableEq D] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem early_addresses_ne (p : OpeningAddress) :
    (earlyParent p : Point) ≠ earlyChild p := by
  intro h
  have he := congrArg (fun q : HPoint => q.role.slot) (Sum.inl.inj (Sum.inr.inj h))
  rw [(CanonicalSecondary125.initialOf p).property, p.property] at he
  simp [Rounds.Role.slot] at he

/-- An opening-first address carries the full context for its initial
draw. The escape and compatibility events read one raw answer each. -/
def earlyEscape (p : OpeningAddress) (cut : (D × D) × List (Enc × D)) (coin : C) : Prop :=
  HashFieldProfile125.secondaryEscape Side (sigAt represent publicOf p.val cut) coin

def earlyCompatible (p : OpeningAddress) (cut : (D × D) × List (Enc × D)) (coin : C) : Prop :=
  compatible Side (sigAt represent publicOf p.val cut) coin

local notation "OpeningMessages" => Fin (Rounds.Role.length (v7HashRow i).params.nl
  (v7HashRow i).params.rounds) → MsgH

def initialAddress (init : Init) : Point := address init.val

private def lateOpening (init : Init) (messages : OpeningMessages) : HPoint :=
  ⟨init.val.ctx, .ligeroQuery, messages⟩

def lateAddress (init : Init) (messages : OpeningMessages) : Point :=
  address (lateOpening init messages)

omit [Inhabited D] [DecidableEq D] [Inhabited MsgH] [DecidableEq K] [DecidableEq Early]
  [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem late_addresses_ne (p : Init) (r : OpeningMessages) :
    (lateAddress p r : Point) ≠ initialAddress p := by
  intro he
  have hh := congrArg (fun q : HPoint => q.role.slot) (Sum.inl.inj (Sum.inr.inj he))
  change (Rounds.Role.ligeroQuery : Rounds.Role (v7HashRow i).params.nl
    (v7HashRow i).params.rounds).slot = p.val.role.slot at hh
  rw [p.property] at hh
  simp [Rounds.Role.slot] at hh

def localOracle (H : Point → C) (p : HPoint) : C := H (address p)

noncomputable def lateSig (H : Point → C) (p : Init) : Sig D C X Enc :=
  sigAt represent publicOf p.val (cutAt S mt H (S.key (initialAddress p)))

variable (wire : ∀ σ : Sig D C X Enc,
  CanonicalHashPrefix125.FieldMessages ((HashCut125.side Side).V σ)
    (v7HashRow i).params.nl (v7HashRow i).params.rounds)

def lateEligible (p : Init) (r : OpeningMessages) (H : Point → C) : Prop :=
  let σ := lateSig S mt represent publicOf H p
  HashFieldProfile125.eligible Side σ (wire σ) (highReply Side σ (wire σ))
    p.val.ctx (localOracle H) p.val (lateOpening p r)

def lateEscape (p : Init) (H : Point → C) (coin : C) : Prop :=
  HashFieldProfile125.secondaryEscape Side (lateSig S mt represent publicOf H p) coin

def lateOpens (p : Init) (r : OpeningMessages) (H : Point → C) (coin : C) : Prop :=
  let σ := lateSig S mt represent publicOf H p
  HashFieldProfile125.eligible Side σ (wire σ)
    (fun lift built batch msg => highReply Side σ (wire σ) lift built batch msg ∧
      ∃ sys, built = some sys ∧ decodedAccepts Side σ sys batch msg coin)
    p.val.ctx (localOracle H) p.val (lateOpening p r)

omit [Fintype C] [Inhabited MsgH] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateSig_opening_off (hkey : S.key = key2) (p : Init) (r : OpeningMessages)
    (H H' : Point → C) (hoff : AgreeOff (lateAddress p r) H H') :
    lateSig S mt represent publicOf H p = lateSig S mt represent publicOf H' p := by
  unfold lateSig
  have hk : S.key (lateAddress p r) = S.key (initialAddress p) := by rw [hkey]; rfl
  rw [← hk, cutAt_off S mt _ _ _ hoff]

omit [Fintype C] [Inhabited D] [DecidableEq D] [Inhabited MsgH] [DecidableEq K]
  [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem localOracle_agreeOff (p : HPoint) (H H' : Point → C)
    (h : AgreeOff (address p) H H') : AgreeOff p (localOracle H) (localOracle H') :=
  fun _ hne => h _ (fun he => hne (Sum.inl.inj (Sum.inr.inj he)))

omit [Inhabited MsgH] [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateinit_off (p : Init) (H H' : Point → C)
    (hoff : AgreeOff (initialAddress p) H H') (coin : C) :
      lateEscape Side S mt represent publicOf p H coin ↔ lateEscape Side S mt represent publicOf p H' coin := by
  unfold lateEscape lateSig
  rw [cutAt_off S mt _ _ _ hoff]

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateEligible_off (hkey : S.key = key2) (p : Init) (r : OpeningMessages)
    (H H' : Point → C) (hoff : AgreeOff (lateAddress p r) H H') (s : OpeningMessages) :
    lateEligible Side S mt represent publicOf wire p s H ↔
      lateEligible Side S mt represent publicOf wire p s H' := by
  unfold lateEligible
  dsimp only
  rw [← lateSig_opening_off S mt represent publicOf hkey p r H H' hoff]
  exact HashFieldProfile125.eligible_off_opening Side _ _ _ _ _ _
    (lateOpening p r) rfl (localOracle_agreeOff _ _ _ hoff)

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateEligible_unique
    (hencoding : ∀ σ {a b}, (wire σ).valid .ligeroQuery a → (wire σ).valid .ligeroQuery b →
      Side.respOf a = Side.respOf b → a = b)
    (p : Init) (H : Point → C) (r s : OpeningMessages)
    (hr : lateEligible Side S mt represent publicOf wire p r H)
    (hs : lateEligible Side S mt represent publicOf wire p s H) : r = s := by
  let σ := lateSig S mt represent publicOf H p
  have he := HashFieldProfile125.eligible_unique Side σ (wire σ)
    (highReply Side σ (wire σ)) (highReply_unique Side σ (wire σ) (hencoding σ))
    p.val.ctx (localOracle H) p.val (lateOpening p r) (lateOpening p s) hr hs
  exact congrArg MPoint.msgs he

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateOpens_off (hkey : S.key = key2) (p : Init) (r : OpeningMessages)
    (H H' : Point → C) (hoff : AgreeOff (lateAddress p r) H H') (coin : C) :
    lateOpens Side S mt represent publicOf wire p r H coin ↔
      lateOpens Side S mt represent publicOf wire p r H' coin := by
  unfold lateOpens
  dsimp only
  rw [← lateSig_opening_off S mt represent publicOf hkey p r H H' hoff]
  exact HashFieldProfile125.eligible_off_opening Side _ _ _ _ _ _
    (lateOpening p r) rfl (localOracle_agreeOff _ _ _ hoff)

open LfzkV1.NizkZk (state_congrG)

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] in
/-- Equal last hash addresses expose the same complete message prefix,
hence the same built rows, batch answer and response. -/
private theorem same_terminal_transcript (σ : Sig D C X Enc)
    (ctx : SideCtx D K Early) (oracle : HPoint → C) (a b : ℕ → MsgH)
    (he : (msgPoint ctx (fun ms j => ms j) a
      (Rounds.Role.ligeroQuery : Rounds.Role (v7HashRow i).params.nl
        (v7HashRow i).params.rounds).slot : HPoint) =
      msgPoint ctx (fun ms j => ms j) b
        (Rounds.Role.ligeroQuery : Rounds.Role (v7HashRow i).params.nl
          (v7HashRow i).params.rounds).slot) :
    let V := (HashCut125.side Side).V σ
    let ta := HashFieldProfile125.pointTape ctx oracle a
    let tb := HashFieldProfile125.pointTape ctx oracle b
    let batch := (Rounds.Role.ligeroChallenge : Rounds.Role (v7HashRow i).params.nl
      (v7HashRow i).params.rounds)
    let last := (Rounds.Role.ligeroQuery : Rounds.Role (v7HashRow i).params.nl
      (v7HashRow i).params.rounds)
    zkBuilt (w := (v7HashRow i).params.rounds) V a ta = zkBuilt V b tb ∧
      ta batch.index = tb batch.index ∧ a last.slot = b last.slot := by
  dsimp only
  let R := v7HashRow i
  let V := (HashCut125.side Side).V σ
  let batch : Rounds.Role R.params.nl R.params.rounds := .ligeroChallenge
  let last : Rounds.Role R.params.nl R.params.rounds := .ligeroQuery
  let ta := HashFieldProfile125.pointTape ctx oracle a
  let tb := HashFieldProfile125.pointTape ctx oracle b
  have hm (j : ℕ) (hj : j ≤ last.slot) : a j = b j := by
    have h := congrArg (fun p : HPoint => p.msgFn j) he
    have ha := msgFn_msgPoint ctx (fun (ms : ℕ → MsgH) k => ms k) a last.slot_lt hj
    have hb := msgFn_msgPoint ctx (fun (ms : ℕ → MsgH) k => ms k) b last.slot_lt hj
    exact ha.symm.trans (h.trans hb)
  have hAll : ∀ j : Fin (Rounds.Role.length R.params.nl R.params.rounds), j.val ≤ last.slot := by
    intro j
    have h := j.isLt
    change j.val < Rounds.Role.layerBase R.params.rounds R.params.nl + 3 at h
    change j.val ≤ Rounds.Role.layerBase R.params.rounds R.params.nl + 2
    omega
  have ht : ta = tb := by
    funext j
    apply congrArg oracle
    exact CanonicalOpening125.msgPoint_eq_of_prefix ctx (fun k hk => hm k (hk.trans (hAll j)))
  have hbatch : batch.slot < last.slot := by simp [batch, last, Rounds.Role.slot]
  have hbound : batch.slot ≤ Rounds.Role.length R.params.nl R.params.rounds := batch.slot_lt.le
  have hstate := state_congrG (nl := R.params.nl) (w := R.params.rounds)
    (LfzkV1.CompiledZkDeployedHash.zkRun_msgLocal (nl := R.params.nl) (w := R.params.rounds)
      V (fun _ _ _ _ => ∅))
    batch.slot (fun j hj => hm j (hj.trans hbatch).le) (Bcs.trunc ta batch.slot hbound)
  have hbld : zkBuilt V a ta = zkBuilt V b tb := by
    rw [← ht]
    exact congrArg builtOf hstate
  exact ⟨hbld, congrFun ht _, hm _ le_rfl⟩

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem lateOpens_sum_le (p : Init) (r : OpeningMessages) (H : Point → C)
    (h : lateEligible Side S mt represent publicOf wire p r H) :
    (∑ coin : C, if lateOpens Side S mt represent publicOf wire p r H coin then (1 : ℚ) else 0) ≤
      Fintype.card C * (1 / 2 ^ 108) := by
  let σ := lateSig S mt represent publicOf H p
  let V := (HashCut125.side Side).V σ
  let ro : HPoint → C := localOracle H
  let ctx := p.val.ctx
  let R := v7HashRow i
  let batchRole : Rounds.Role R.params.nl R.params.rounds := .ligeroChallenge
  let last : Rounds.Role R.params.nl R.params.rounds := .ligeroQuery
  obtain ⟨lift, hsec, a, ha, hp⟩ :=
    HashFieldProfile125.eligible_reply_at Side σ (wire σ) (highReply Side σ (wire σ))
      ctx ro p.val (lateOpening p r) h
  let challenge := V.decodeChal (HashFieldProfile125.pointTape ctx ro a batchRole.index)
  obtain ⟨sys, hsys, haValid, haHigh⟩ := ha
  have hhigh : highReply Side σ (wire σ) lift (some sys) challenge (a last.slot) :=
    ⟨sys, rfl, haValid, haHigh⟩
  refine (Finset.sum_le_sum (g := fun c => @ite ℚ (decodedAccepts Side σ sys challenge (a last.slot) c)
    (Classical.propDecidable _) 1 0) ?_).trans (decodedAccepts_sum_le Side σ (wire σ)
      lift hsec sys challenge (a last.slot) hhigh)
  intro coin _
  by_cases hh : lateOpens Side S mt represent publicOf wire p r H coin
  · obtain ⟨other, ho, b, ⟨_, sys', hsys', hpass⟩, hp'⟩ :=
      HashFieldProfile125.eligible_reply_at Side σ (wire σ) _ ctx ro p.val (lateOpening p r) hh
    obtain ⟨hbld, hbatch, hmsg⟩ := same_terminal_transcript Side σ ctx ro a b (hp.symm.trans hp')
    have hsame : sys = sys' := Option.some.inj (hsys.symm.trans (hbld.trans hsys'))
    have hdecoded : decodedAccepts Side σ sys challenge (a last.slot) coin := by
      rwa [hsame, hmsg, show challenge = V.decodeChal
        (HashFieldProfile125.pointTape ctx ro b batchRole.index) by exact congrArg V.decodeChal hbatch]
    simp only [if_pos hh, if_pos hdecoded, le_refl]
  · simp only [if_neg hh]
    split <;> positivity

private noncomputable def addressOrder (H : Point → C) (a b : Point) : FirstOfTwo :=
  firstOfTwo (S.search mt) H a b

def OpeningFirstEvent (H : Point → C) (p : OpeningAddress) : Prop :=
  addressOrder S mt H (earlyParent p) (earlyChild p) = .right ∧
    earlyEscape Side represent publicOf p (cutAt S mt H (S.key (earlyParent p)))
      (H (earlyParent p)) ∧
    earlyCompatible Side represent publicOf p (cutAt S mt H (S.key (earlyParent p)))
      (H (earlyChild p))

def InitialFirstEvent (H : Point → C) (p : Init) (r : OpeningMessages) : Prop :=
  (addressOrder S mt H (initialAddress p) (lateAddress p r) = .left ∧
    lateEligible Side S mt represent publicOf wire p r H ∧
    lateEscape Side S mt represent publicOf p H (H (initialAddress p))) ∧
    lateOpens Side S mt represent publicOf wire p r H (H (lateAddress p r))

def CanonicalEvent (H : Point → C) : Prop :=
  (∃ p, OpeningFirstEvent Side S mt represent publicOf H p) ∨
    ∃ p r, InitialFirstEvent Side S mt represent publicOf wire H p r

local notation "BatchRole" => (Rounds.Role.ligeroChallenge :
  Rounds.Role (v7HashRow i).params.nl (v7HashRow i).params.rounds)
local notation "LastRole" => (Rounds.Role.ligeroQuery :
  Rounds.Role (v7HashRow i).params.nl (v7HashRow i).params.rounds)

noncomputable def submittedInit (ctx : SideCtx D K Early) (msgs : ℕ → MsgH) : Init :=
  ⟨msgPoint ctx (fun f j => f j) msgs 0,
    slot_msgPoint ctx (fun f j => f j) msgs (by simp [Rounds.Role.length])⟩

noncomputable def submittedOpening (ctx : SideCtx D K Early) (msgs : ℕ → MsgH) : OpeningAddress :=
  ⟨msgPoint ctx (fun f j => f j) msgs (LastRole).slot,
    Rounds.Role.slot_inj
      (LfzkV1.NizkGrinding.slot_roleAt (LastRole).slot_lt)⟩

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
/-- A submitted secondary canonical path with a queried initial address
is covered by the two orders at its actual transcript addresses. -/
theorem canonical_secondary_cover (H : Point → C)
    (ctx : SideCtx D K Early) (msgs : ℕ → MsgH)
    (hobs : initialAddress (submittedInit ctx msgs) ∈ queried (S.search mt) H)
    (lift : Lift (lateSig S mt represent publicOf H (submittedInit ctx msgs)))
    (hmsg : let σ := lateSig S mt represent publicOf H (submittedInit ctx msgs)
      ∀ role : Rounds.Role (v7HashRow i).params.nl (v7HashRow i).params.rounds,
        (wire σ).valid role (msgs role.slot))
    (hcanonical : HashFieldProfile125.canonicalSecondary Side
      (lateSig S mt represent publicOf H (submittedInit ctx msgs)) msgs
      (HashFieldProfile125.pointTape ctx (localOracle H) msgs) lift)
    (haccept : let σ := lateSig S mt represent publicOf H (submittedInit ctx msgs)
      let V := (HashCut125.side Side).V σ
      let tape := HashFieldProfile125.pointTape ctx (localOracle H) msgs
      let batch := V.decodeChal (tape (BatchRole).index)
      let response := msgs (LastRole).slot
      highReply Side σ (wire σ) lift (zkBuilt (w := (v7HashRow i).params.rounds) V msgs tape)
        batch response ∧
      (∃ sys, zkBuilt V msgs tape = some sys ∧ decodedAccepts Side σ sys batch response
        (H (earlyChild (submittedOpening ctx msgs)))) ∧
      LiftOpening125.Compatible lift (decodeQuery Side σ
        (H (earlyChild (submittedOpening ctx msgs)))) (cert i).g) :
    CanonicalEvent Side S mt represent publicOf wire H := by
  let p := submittedInit (i := i) ctx msgs
  let o := submittedOpening (i := i) ctx msgs
  let σ := lateSig S mt represent publicOf H p
  let r := o.val.msgs
  have hparent : (earlyParent o : Point) = initialAddress p := by
    unfold earlyParent initialAddress
    exact congrArg address (CanonicalSecondary125.initialOf_eq (p := o) rfl)
  have hopen : lateOpening p r = o.val := by
    change MPoint.mk p.val.ctx .ligeroQuery o.val.msgs = o.val
    have hc : p.val.ctx = o.val.ctx := rfl
    rw [hc]
    exact congrArg (fun role => MPoint.mk o.val.ctx role o.val.msgs) o.property.symm
  have hchild : (lateAddress p r : Point) = earlyChild o := congrArg address hopen
  have hσ : sigAt represent publicOf o.val (cutAt S mt H (S.key (earlyParent o))) = σ := by
    rw [hparent]
    rfl
  let tape : Fin (Rounds.Role.length (v7HashRow i).params.nl (v7HashRow i).params.rounds) → C :=
    HashFieldProfile125.pointTape ctx (localOracle H) msgs
  change HashFieldProfile125.canonicalSecondary Side σ msgs tape lift at hcanonical
  have hsec : HashFieldProfile125.primary Side σ ≠ some lift :=
    (HashFieldProfile125.canonicalSecondary_init Side σ msgs tape lift hcanonical).1
  have hesc := HashFieldProfile125.secondaryEscape_of_canonicalSecondary Side σ msgs tape lift hcanonical
  change lateEscape Side S mt represent publicOf p H (H (initialAddress p)) at hesc
  obtain ⟨hhigh, hpass, hcompatible⟩ := haccept
  have hord := CanonicalOpening125.firstOfTwo_of_initial_observed (S.search mt) H
      (initialAddress p) (earlyChild o) hobs
  change addressOrder S mt H (initialAddress p) (earlyChild o) = .left ∨
    addressOrder S mt H (initialAddress p) (earlyChild o) = .right at hord
  rcases hord with hl | ho
  · right
    refine ⟨p, r, ⟨?_, ?_, hesc⟩, ?_⟩
    · rwa [hchild]
    · unfold lateEligible
      rw [hopen]
      exact HashFieldProfile125.eligible_of_canonicalSecondary Side σ (wire σ)
        (highReply Side σ (wire σ)) ctx (localOracle H) lift msgs hmsg hcanonical hhigh
    · unfold lateOpens
      rw [hopen, hchild]
      exact HashFieldProfile125.eligible_of_canonicalSecondary Side σ (wire σ)
        _ ctx (localOracle H) lift msgs hmsg hcanonical ⟨hhigh, hpass⟩
  · left
    refine ⟨o, ?_, ?_, ?_⟩
    · rwa [hparent]
    · unfold earlyEscape
      rw [hσ, hparent]
      exact hesc
    · unfold earlyCompatible
      rw [hσ]
      exact ⟨lift, hsec, hcompatible⟩

section Count

variable [Fintype D] [Fintype K] [Fintype Early] [Fintype MsgH] [Fintype MsgS] [Nonempty C]

open LfzkV1.LigeroOrder125 (indicator)

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
/-- The opening-first secondary event is paid at the actual opening
address. Only the 7/q initial escape and the 2^-32 compatible-opening
fraction enter its contribution. -/
theorem openingFirst_sum_le (hkey : S.key = key2) :
    (∑ H : Point → C, ∑ p : OpeningAddress,
      indicator (OpeningFirstEvent Side S mt represent publicOf H p)) ≤
      (7 / 2^128) * (1 / 2^32) * ∑ H : Point → C, ∑ p : OpeningAddress,
        indicator (addressOrder S mt H (earlyParent p) (earlyChild p) = .right) := by
  have hs (p : OpeningAddress) : S.key (earlyParent p) = S.key (earlyChild p) := by
    rw [hkey]
    rfl
  have ho := CanonicalOpening125.openingFirst_cut_sum_le (I := OpeningAddress) (Q := Point)
    (S.search mt) earlyParent earlyChild
    early_addresses_ne S.key (cutAt S mt) hs (cutAt_off S mt)
    (earlyEscape Side represent publicOf) (earlyCompatible Side represent publicOf)
    (7 / 2^128) (1 / 2^32) (by positivity)
    (fun p ct => HashFieldProfile125.secondaryEscape_sum_le Side (sigAt represent publicOf p.val ct))
    (fun p ct => compatible_sum_le Side (sigAt represent publicOf p.val ct))
  exact ho

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
/-- The initial-first canonical event retains the number of observed initial
inputs for the common field query budget. -/
theorem initialFirst_sum_le (hkey : S.key = key2)
    (hencoding : ∀ σ {a b}, (wire σ).valid .ligeroQuery a → (wire σ).valid .ligeroQuery b →
      Side.respOf a = Side.respOf b → a = b) :
    (∑ H : Point → C, ∑ p : Init, ∑ r : OpeningMessages,
      indicator (InitialFirstEvent Side S mt represent publicOf wire H p r)) ≤
      (7 / 2^128) * (1 / 2^108) * ∑ H : Point → C, ∑ p : Init,
        indicator ((initialAddress p : Point) ∈ queried (S.search mt) H) := by
  have escapeOffOpen (p : Init) (r : OpeningMessages) (H H' : Point → C)
      (hoff : AgreeOff (lateAddress p r) H H') (coin : C) :
      lateEscape Side S mt represent publicOf p H coin ↔
        lateEscape Side S mt represent publicOf p H' coin := by
    unfold lateEscape
    rw [lateSig_opening_off S mt represent publicOf hkey p r H H' hoff]
  have hl := @CanonicalSecondary125.parent_first_charge_le Point Init OpeningMessages C Out
    _ _ _ _ _ _ N (S.search mt) initialAddress lateAddress
    late_addresses_ne (lateEligible Side S mt represent publicOf wire)
    (lateEscape Side S mt represent publicOf)
    (lateOpens Side S mt represent publicOf wire)
    (lateEligible_unique Side S mt represent publicOf wire hencoding)
    (lateEligible_off Side S mt represent publicOf wire hkey)
    (lateinit_off Side S mt represent publicOf) escapeOffOpen
    (fun p r H H' hoff _ coin => lateOpens_off Side S mt represent publicOf wire hkey p r H H' hoff coin)
    (7 / 2^128) (1 / 2^108) (by positivity)
    (fun p H => HashFieldProfile125.secondaryEscape_sum_le Side (lateSig S mt represent publicOf H p))
    (lateOpens_sum_le Side S mt represent publicOf wire)
  exact hl

open LfzkV1.TwoFieldCover125 (QueryRole queryRole observedRole observed_image_count_le)

private theorem order_right_count_le (H : Point → C) :
    (∑ p : OpeningAddress, indicator (addressOrder S mt H (earlyParent p) (earlyChild p) = .right)) ≤
      (observedRole (S.search mt) .opening H).card := by
  let seen (p : OpeningAddress) := addressOrder S mt H (earlyParent p) (earlyChild p) = .right
  letI : DecidablePred seen := fun p => Classical.propDecidable (seen p)
  let labels := univ.filter seen
  have hinj : Function.Injective (earlyChild : OpeningAddress → Point) :=
    fun _ _ h => Subtype.ext (Sum.inl.inj (Sum.inr.inj h))
  have hrole (p : OpeningAddress) : queryRole (earlyChild p : Point) = .opening := by
    simp [queryRole, earlyChild, address, p.property]
  calc
    _ = (labels.card : ℚ) := by simp [indicator, labels, seen]
    _ ≤ _ := observed_image_count_le (S.search mt) H earlyChild hinj .opening hrole labels
      fun p hp => firstOfTwo_right_mem (S.search mt) H (earlyParent p) (earlyChild p)
        (mem_filter.mp hp).2

omit [Inhabited MsgH] in
private theorem initial_count_le (H : Point → C) :
    (∑ p : Init, indicator ((initialAddress p : Point) ∈ queried (S.search mt) H)) ≤
      (observedRole (S.search mt) .field H).card := by
  let seen (p : Init) := (initialAddress p : Point) ∈ queried (S.search mt) H
  letI : DecidablePred seen := fun p => Classical.propDecidable (seen p)
  let labels := univ.filter seen
  have hinj : Function.Injective (initialAddress : Init → Point) :=
    fun _ _ h => Subtype.ext (Sum.inl.inj (Sum.inr.inj h))
  have hrole (p : Init) : queryRole (initialAddress p : Point) = .field := by
    have hp := p.property
    cases h : p.val.role <;> simp [queryRole, initialAddress, address, h]
    all_goals
      rw [h, Rounds.Role.slot] at hp
      exact (Nat.succ_ne_zero _ hp).elim
  calc
    _ = (labels.card : ℚ) := by simp [indicator, labels, seen]
    _ ≤ _ := observed_image_count_le (S.search mt) H initialAddress hinj .field hrole labels
      fun _ hp => (mem_filter.mp hp).2

private theorem exists_indicator_le {A : Type} [Fintype A] (P : A → Prop) :
    indicator (∃ a, P a) ≤ ∑ a, indicator (P a) := by
  unfold indicator
  by_cases he : ∃ a, P a
  · obtain ⟨a, ha⟩ := he
    rw [if_pos ⟨a, ha⟩]
    have h := single_le_sum (f := fun b => if P b then (1 : ℚ) else 0)
      (fun b _ => by split <;> norm_num) (mem_univ a)
    simpa only [ha, if_true] using h
  · rw [if_neg he]
    exact sum_nonneg fun a _ => by split <;> norm_num

/-- The canonical secondary event charges the opening or field role at
the first of its two registered addresses. -/
theorem canonical_count_le (hkey : S.key = key2)
    (hencoding : ∀ σ {a b}, (wire σ).valid .ligeroQuery a → (wire σ).valid .ligeroQuery b →
      Side.respOf a = Side.respOf b → a = b) :
    (∑ H : Point → C, indicator (CanonicalEvent Side S mt represent publicOf wire H)) ≤
      (7 / 2^128) * (1 / 2^32) * ∑ H : Point → C,
        ((observedRole (S.search mt) .opening H).card : ℚ) +
      (7 / 2^128) * (1 / 2^108) * ∑ H : Point → C,
        ((observedRole (S.search mt) .field H).card : ℚ) := by
  let early (H : Point → C) (p : OpeningAddress) := OpeningFirstEvent Side S mt represent publicOf H p
  let late (H : Point → C) (p : Init) (r : OpeningMessages) :=
    InitialFirstEvent Side S mt represent publicOf wire H p r
  have he : (∑ H, ∑ p, indicator (early H p)) ≤
      (7 / 2^128) * (1 / 2^32) * ∑ H : Point → C,
        ((observedRole (S.search mt) .opening H).card : ℚ) :=
    (openingFirst_sum_le Side S mt represent publicOf hkey).trans
      (mul_le_mul_of_nonneg_left (sum_le_sum fun _ _ => order_right_count_le S mt _) (by positivity))
  have hl : (∑ H, ∑ p, ∑ r, indicator (late H p r)) ≤
      (7 / 2^128) * (1 / 2^108) * ∑ H : Point → C,
        ((observedRole (S.search mt) .field H).card : ℚ) :=
    (initialFirst_sum_le Side S mt represent publicOf wire hkey hencoding).trans
      (mul_le_mul_of_nonneg_left (sum_le_sum fun _ _ => initial_count_le S mt _) (by positivity))
  refine le_trans ?_ (add_le_add he hl)
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro H _
  have hx := exists_indicator_le (early H)
  have hy := (exists_indicator_le (fun p => ∃ r, late H p r)).trans
    (sum_le_sum fun p _ => exists_indicator_le (late H p))
  refine le_trans ?_ (add_le_add hx hy)
  change indicator ((∃ p, early H p) ∨ (∃ p r, late H p r)) ≤
    indicator (∃ p, early H p) + indicator (∃ p r, late H p r)
  by_cases he' : ∃ p, early H p <;> by_cases hl' : ∃ p r, late H p r <;>
    norm_num [indicator, he', hl']

end Count

end Search

end LfzkV1.HashCanonicalCharge125
