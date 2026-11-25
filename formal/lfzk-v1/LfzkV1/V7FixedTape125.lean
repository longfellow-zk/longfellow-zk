import LfzkV1.HashCanonicalCharge125
import LfzkV1.HashSearchField125
import LfzkV1.ReplayInputs125
import LfzkV1.SoundnessCompose125
import LfzkV1.TerminalCharge125
import LfzkV1.V7ReplayCharge125

/-! The covered cases and remaining hash replay on one fixed Merkle tape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.V7FixedTape125

open Finset Bcs.TotalOracle Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
open LfzkV1.CertifiedV1 LfzkV1.CompiledZk LfzkV1.CompiledZkDeployedHash
open LfzkV1.CompiledLongfellow (Col ligIdx qryIdx)
open LfzkV1.CompiledLongfellowAdaptive (Sig slice1 slice2)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField LfzkV1.NizkZk
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.SoundnessAudit LfzkV1.TwoFieldCover125 LfzkV1.TwoFieldV1Rows
open LfzkV1.HashCircuitReplay125 LfzkV1.LiftOpening125 LfzkV1.MacSep
open LfzkV1.LigeroHighMass125 (liftedResponses highCutoff)
open scoped Classical

variable {C D Enc Early HashPublic SigPublic SaltH SaltS Fmac Fh Fs MsgH MsgS Out : Type}
variable [Fintype C] [Nonempty C] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable [Inhabited SaltH] [Inhabited SaltS]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable [Field Fh] [Fintype Fh] [DecidableEq Fh] [SumcheckV1Interp Fh]
variable [Field Fs] [Fintype Fs] [DecidableEq Fs] [SumcheckV1Interp Fs]
variable [Inhabited MsgH] [Inhabited MsgS]
variable {Mh Ms nth nts nlinh nlins nblk tA N TM fc : ℕ} {i : Fin 4}
variable {hH : (v7HashRow i).Valid} {hrH : 0 < (v7HashRow i).params.row.openings}
variable {hS : v7SigHahn.Valid}
variable {codecH : Codec SaltH (Col Fh (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {codecS : Codec SaltS (Col Fs v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {decH : RoleDecoders codecH} {decS : RoleDecoders codecS}
variable (Hash : CircuitSide (v7HashRow i) hH hrH (v7HashLogv i)
  C Fh MsgH Mh nth nlinh HashPublic decH Prod.fst)
variable (Signature : CircuitSide v7SigHahn hS v7SigHahn_openings_pos 8
  C Fs MsgS Ms nts nlins SigPublic decS Prod.snd)

local notation "R" => v7HashRow i
local notation "Pt" => SignatureBudget125.PairPoint D Fmac Early MsgH MsgS (v7HashRow i)
abbrev HashRoleAt (j : Fin 4) := Rounds.Role (v7HashRow j).params.nl (v7HashRow j).params.rounds
local notation "HashRole" => HashRoleAt i
local notation "Lift" => sideLiftAt Hash (HashCut125.radius i)

variable (body : TwoOracleTree Enc D
    (SignatureBudget125.PairPoint D Fmac Early MsgH MsgS (v7HashRow i)) C Out tA N)
variable (rootH rootS : Out → D) (avOf : Out → Fmac) (earlyOf : Out → Early)
variable (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → MsgS)
variable (mt : Fin TM → D)
variable (represent : Fmac → C) (hashPublic : Early → HashPublic) (sigPublic : Out → SigPublic)

local notation "A" => setup2 body rootH rootS avOf earlyOf msgH msgS
local notation "hashPubOf" => hashPublic ∘ earlyOf

/-- The cut, decoded-share representative and early public inputs in the
hash-side extraction. -/
noncomputable def hashSig (H : Pt → C) : Sig D C HashPublic Enc :=
  sideCtx (A) (represent ∘ avOf) hashPubOf mt H

noncomputable def hashTape (H : Pt → C) : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C :=
  slice1 (R) v7SigHahn ((A).challenges mt H)

variable (d : ExactDecoder C Fmac)
variable (commonH shareH : (Fin Hash.c.ninp → Fh) → Fin nblk → Fmac)
variable (commonS shareS : (Fin Signature.c.ninp → Fs) → Fin nblk → Fmac)
variable (shift : Cut D Enc → Fmac)

def macCase (H : Pt → C) : Prop :=
  let k := (A).context mt H
  MacCharge125.badKey (Signature.cands k) (Hash.candsAt (HashCut125.radius i) k)
    commonS commonH shareS shareH (shift k) (d.decode (H ((A).hashInput ((A).proof mt H) 0)))

def fieldCase (H : Pt → C) : Prop :=
  ∃ p ∈ observedRole ((A).search mt) .field H,
    HashSearchField125.bad Hash (A) mt represent hashPublic H p (H p)

local notation "sigma" => hashSig body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic
local notation "tape" => hashTape body rootH rootS avOf earlyOf msgH msgS mt

def ambiguityCase (H : Pt → C) : Prop :=
  let s := sigma H
  let q := (Hash.Vc s.2.1 s.2.2).decodeQuery (tape H qryIdx)
  ∃ x y : Lift s, x ≠ y ∧ Compatible x q (OpeningGeometry125.result i).certificate.g ∧
    Compatible y q (OpeningGeometry125.result i).certificate.g

def terminalCase (H : Pt → C) : Prop :=
  let s := sigma H
  let V := Hash.Vc s.2.1 s.2.2
  let ms := msgH ((A).proof mt H)
  let t := tape H
  let code := (R).params.row.code (Row.rowValid hH) Hash.dom (Row.hkrow hH)
  let cut := extOracle nlinh nth (Row.rowValid hH) Hash.dom (Row.hkrow hH) hrH decH
    (s.1.1.1, s.1.2)
  ∃ sys, zkBuilt (nl := (R).params.nl) (w := (R).params.rounds) V ms t = some sys ∧
    directTerminal i code cut (Encode.encodeLig Hash.pl nlinh sys) (V.decodeChal (t ligIdx))
      (Hash.respOf (ms (Rounds.Role.ligeroQuery : HashRole).slot)) (V.decodeQuery (t qryIdx))

variable (wire : ∀ s : Sig D C HashPublic Enc,
  CanonicalHashPrefix125.FieldMessages ((HashCut125.side Hash).V s)
    (v7HashRow i).params.nl (v7HashRow i).params.rounds)

def canonicalCase (H : Pt → C) : Prop :=
  HashCanonicalCharge125.CanonicalEvent Hash (A) mt represent hashPublic wire H

omit [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] in
/-- A canonical healthy completion either exposes a terminal exception
at its recomputed statement or pays for the secondary lift's opening. -/
theorem canonical_completion (H : Pt → C) (lift : Lift (sigma H))
    (hpass : accepts Hash (sigma H) (msgH ((A).proof mt H)) (tape H) lift)
    (hcomp : Compatible lift ((Hash.Vc (sigma H).2.1 (sigma H).2.2).decodeQuery (tape H qryIdx))
      (OpeningGeometry125.result i).certificate.g)
    (hmsg : ∀ role : HashRole, (wire (sigma H)).valid role (msgH ((A).proof mt H) role.slot))
    (hseen : let out := (A).proof mt H
      ReplayInputs125.sideAddress (msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out 0) ∈
        queried ((A).search mt) H)
    (hcanon : let out := (A).proof mt H
      let ctx := ctxOf rootH rootS avOf earlyOf out
      HashFieldProfile125.canonicalSecondary Hash (sigma H) (msgH out)
        (HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) (msgH out)) lift) :
    terminalCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic H ∨
      ambiguityCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic H ∨
      canonicalCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic wire H := by
  let out := (A).proof mt H
  let s := sigma H
  let ctx := ctxOf rootH rootS avOf earlyOf out
  let messages := msgH out
  obtain ⟨sys, hb, hterm⟩ := terminal_cover_of_replay Hash s messages (tape H) lift hpass
  rcases hterm with hd | ha | ⟨x, hselected, hx, hhigh, hu⟩
  · exact Or.inl ⟨sys, hb, hd⟩
  · exact Or.inr (Or.inl ha)
  have hlift : x = lift := hu lift hcomp
  subst x
  right
  right
  have htape : HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) messages = tape H :=
    (roleTape_addresses ReplayInputs125.sideAddress ctx messages H).symm.trans
      (ReplayInputs125.tape_eq rootH rootS avOf earlyOf msgH msgS body mt H)
  refine HashCanonicalCharge125.canonical_secondary_cover Hash (A) mt represent hashPublic wire H
    ctx messages hseen lift hmsg hcanon ?_
  · dsimp only
    have hb' : zkBuilt (nl := (R).params.nl) (w := (R).params.rounds)
        (Hash.Vc s.2.1 s.2.2) messages
        (HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) messages) = some sys := by
      rw [htape]
      exact hb
    have hqr : H (HashCanonicalCharge125.earlyChild (HashCanonicalCharge125.submittedOpening (i := i)
        ctx messages)) = tape H qryIdx := congrFun htape qryIdx
    have hbatch : HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) messages ligIdx =
        tape H ligIdx := congrFun htape ligIdx
    refine ⟨⟨sys, hb', hmsg .ligeroQuery, ?_⟩, ⟨sys, hb', ?_⟩, ?_⟩
    · change Hash.respOf (messages (Rounds.Role.ligeroQuery : HashRole).slot) ∈
        liftedResponses (Encode.encodeLig Hash.pl nlinh sys) lift (highCutoff i)
          (OpeningGeometry125.result i).certificate.g ((Hash.Vc s.2.1 s.2.2).decodeChal
            (HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) messages ligIdx))
      rw [hbatch]
      exact hhigh
    · change HashCanonicalCharge125.decodedAccepts Hash s sys
        ((Hash.Vc s.2.1 s.2.2).decodeChal
          (HashFieldProfile125.pointTape ctx (H ∘ ReplayInputs125.sideAddress) messages ligIdx))
        (messages (Rounds.Role.ligeroQuery : HashRole).slot) _
      rw [hbatch, hqr]
      obtain ⟨sys', hb'', _, hp⟩ := hselected
      obtain rfl := Option.some.inj (hb.symm.trans hb'')
      exact hp
    · rwa [hqr]

section Count

variable [Fintype D] [Fintype Early] [Fintype MsgH] [Fintype MsgS] [Nonempty HashPublic]
variable [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] [DecidableEq C] [DecidableEq Out]

abbrev HashPrefixAt (j : Fin 4) (D Fmac Early MsgH : Type) [Inhabited MsgH] :=
  TerminalPrefix125.BatchPrefix (SideCtx D Fmac Early) MsgH
    (v7HashRow j).params.nl (v7HashRow j).params.rounds
abbrev HashResponseAt (j : Fin 4) (Fh : Type) := LigeroFamily.Response Fh (v7HashRow j).params.row.openings
  (v7HashRow j).params.q (v7HashRow j).params.row.n 1
local notation "Prefix" => HashPrefixAt i D Fmac Early MsgH
local notation "Response" => HashResponseAt i Fh

set_option maxHeartbeats 3000000 in
/-- At a fixed Merkle tape, the actual explained two-field replay loses
at most the algebraic budget. The two wire premises express how the
submitted raw messages encode the opened mathematical response. -/
theorem fixed_tape_cover_bound {Wire : Type} [Fintype Wire]
    (toResponse : Wire ↪ Response) (wireResponse : Out → Wire)
    (encode : Prefix → Wire → MsgH) (decode : Prefix → MsgH → Option Wire) (valid : Prefix → MsgH → Prop)
    (hdecode : ∀ p u, decode p (encode p u) = some u)
    (hvalid : ∀ p m u, valid p m → decode p m = some u → encode p u = m)
    (hwire : ∀ out,
      let o : TerminalPrefix125.OpeningPoint (SideCtx D Fmac Early) MsgH (R).params.nl (R).params.rounds :=
        TerminalPrefix125.openingOfMessages (ctxOf rootH rootS avOf earlyOf out) (msgH out)
      let m := o.val.msgs TerminalPrefix125.openingIndex
      valid (TerminalPrefix125.parent o) m ∧ decode (TerminalPrefix125.parent o) m = some (wireResponse out) ∧
        toResponse (wireResponse out) = Hash.respOf m)
    (hwmsgs : ∀ s out (role : HashRole), (wire s).valid role (msgH out role.slot))
    (hwresp : ∀ s {a b}, (wire s).valid .ligeroQuery a → (wire s).valid .ligeroQuery b →
      Hash.respOf a = Hash.respOf b → a = b)
    (hmacCard : Fintype.card Fmac = 2^128)
    (event sig : (Pt → C) → Prop)
    (hsig : ((univ.filter sig).card : ℚ) ≤
      ((1426 : ℚ) / (1000 * 2^128)) * ∑ H : Pt → C,
        ((observedRole ((A).search mt) .signature H).card + (1 : ℚ)))
    (hremaining : ∀ H, event H → ¬ sig H →
      ¬ macCase Hash Signature body rootH rootS avOf earlyOf msgH msgS mt d
        commonH shareH commonS shareS shift H →
      ¬ terminalCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic H →
      ¬ ambiguityCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic H →
      let s := sigma H
      let q := (Hash.Vc s.2.1 s.2.2).decodeQuery (tape H qryIdx)
      ∃ x : Lift s, ¬ (HashCut125.side Hash).Sat s x ∧
        accepts Hash s (msgH ((A).proof mt H)) (tape H) x ∧
        Compatible x q (OpeningGeometry125.result i).certificate.g ∧
        ∀ y : Lift s, Compatible y q (OpeningGeometry125.result i).certificate.g → x = y) :
    ((univ.filter event).card : ℚ) / Fintype.card (Pt → C) ≤ (97 + N * (701 / 100)) / 2^128 := by
  classical
  let observe := ReplayView125.view ((A).search mt) (ReplayInputs125.lookups rootH rootS avOf earlyOf msgH)
  let mac := macCase Hash Signature body rootH rootS avOf earlyOf msgH msgS mt d commonH shareH commonS shareS shift
  let fld := fieldCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic
  let term := terminalCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic
  let amb := ambiguityCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic
  let canon := canonicalCase Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic wire
  let cases (j : Fin 6) : (Pt → C) → Prop := match j.val with
    | 0 => mac
    | 1 => sig
    | 2 => fld
    | 3 => term
    | 4 => amb
    | _ => canon
  let covered (H : Pt → C) := ∃ j, cases j H
  let count (role : QueryRole) (H : Pt → C) := (observedRole ((A).search mt) role H).card
  have hF : Fintype.card Fh = 2^128 := by rw [Hash.hF]; fin_cases i <;> rfl
  apply SoundnessCompose125.fixed_tape_ratio_le N observe event covered cases
    (count .key) (count .signature) (count .field) (count .batch) (count .opening)
    (fun _ h => h)
  · intro H
    have h := observed_role_partition_le ((A).search mt) H
    dsimp only [count]
    omega
  · intro j
    fin_cases j
    · simpa [cases, SoundnessCompose125.caseBudget, count, Finset.mul_sum] using
        key_failure_count_le Hash Signature body rootH rootS avOf earlyOf msgH msgS mt d hmacCard
          commonH shareH commonS shareS shift mac (fun _ h => h)
    · simpa [cases, SoundnessCompose125.caseBudget, count, Finset.mul_sum, div_div] using hsig
    · simpa [cases, SoundnessCompose125.caseBudget, count, Finset.mul_sum, fld, fieldCase] using
        HashSearchField125.observed_field_count_le Hash (A) mt represent hashPublic
    · simpa [cases, SoundnessCompose125.caseBudget, count, div_div] using
        TerminalCharge125.compiled_count_le Hash body rootH rootS avOf earlyOf represent hashPublic msgH msgS mt
          hF toResponse wireResponse encode decode valid hdecode hvalid term (fun _ _ => hwire _) (fun _ h => h)
    · simpa [cases, SoundnessCompose125.caseBudget, count] using
        TerminalCharge125.compiled_ambiguity_count_le Hash body rootH rootS avOf earlyOf represent hashPublic
          msgH msgS mt amb (fun _ h => h)
    · have hc := HashCanonicalCharge125.canonical_count_le Hash (A) mt represent hashPublic wire rfl hwresp
      simp only [LigeroOrder125.indicator] at hc
      rw [← Finset.sum_filter] at hc
      simpa [cases, SoundnessCompose125.caseBudget, count, canon, canonicalCase,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
        div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hc
  · intro v _
    let ctx := ctxOf rootH rootS avOf earlyOf
    let embed : HashFieldProfile125.HashPoint i (SideCtx D Fmac Early) MsgH ↪ Pt := ReplayInputs125.sideAddress
    have hview : _ := V7ReplayCharge125.view_split_le Hash ((A).search mt)
      (ReplayInputs125.lookups rootH rootS avOf earlyOf msgH) embed ctx msgH sigma event covered
      ?_ ?_ ?_ ?_ ?_ ?_ v
    · simp only [V7ReplayCharge125.sampleCount] at hview
      rcases hview with hh | hh
      · left
        convert hh using 2
        first
          | rfl
          | apply congrArg (fun s : Finset (Pt → C) => (s.card : ℚ))
            ext U
            simp [observe]
      · right
        convert hh using 2
    · intro H
      simpa only [← (A).proof_eq mt H, ReplayInputs125.points, embed, ctx] using
        ReplayInputs125.terminal_revealed rootH rootS avOf earlyOf msgH msgS body mt H
    · exact ReplayInputs125.field_not_replayed rootH rootS avOf earlyOf msgH
    · intro H U hv
      obtain ⟨hout, hcut⟩ := ReplayInputs125.view_fixes_output_and_cut rootH rootS avOf earlyOf msgH msgS body mt H U hv
      unfold hashSig sideCtx
      rw [hout, hcut]
    · intro H hE hN
      have hl := hremaining H hE (fun h => hN ⟨1, h⟩) (fun h => hN ⟨0, h⟩)
        (fun h => hN ⟨3, h⟩) (fun h => hN ⟨4, h⟩)
      simpa only [← ReplayInputs125.tape_eq rootH rootS avOf earlyOf msgH msgS body mt H,
        (A).proof_eq mt H, ReplayInputs125.points, embed, ctx, hashTape] using hl
    · intro H U hv
      dsimp only
      intro hp
      obtain ⟨hout, hcut⟩ := ReplayInputs125.view_fixes_output_and_cut rootH rootS avOf earlyOf msgH msgS body mt H U hv
      obtain ⟨j, hseen, hb⟩ := hp
      let out := (A).proof mt U
      let point (o : Out) : HashFieldProfile125.HashPoint i (SideCtx D Fmac Early) MsgH :=
        msgPoint (ctx o) msgH o j.val
      let p := embed (point out)
      have hrun : ((A).search mt).run U = ((A).search mt).run H := congrArg Prod.fst hv
      have ho : (((A).search mt).run H).1 = out := ((A).proof_eq mt H).symm.trans hout.symm
      have hbad : HashSearchField125.bad Hash (A) mt represent hashPublic U p (U p) := by
        have hs : sigma U = sigma H := by unfold hashSig sideCtx; rw [hout, hcut]
        change HashFieldProfile125.bad Hash (sigma U) (point out) (mpoints.chal (U ∘ embed) (point out)) (U p)
        rw [hs]
        let badAt (o : Out) : Prop := HashFieldProfile125.bad Hash (sigma H) (point o)
          (mpoints.chal (U ∘ embed) (point o)) (U (embed (point o)))
        change badAt (((A).search mt).run H).1 at hb
        change badAt out
        exact ho ▸ hb
      have hobs : p ∈ queried ((A).search mt) H := by
        dsimp only [p]
        rw [← ho]
        exact hseen
      have hqueried : queried ((A).search mt) U = queried ((A).search mt) H :=
        congrArg (fun r => r.2.map Prod.fst) hrun
      have hmem : p ∈ observedRole ((A).search mt) .field U := by
        simp only [observedRole, MacCharge125.observedKeys, mem_filter, List.mem_toFinset, hqueried]
        exact ⟨hobs, HashSearchField125.field_role_of_bad Hash (A) mt represent hashPublic U p (U p) hbad⟩
      exact ⟨2, ⟨p, hmem, hbad⟩⟩
    · intro H U hv
      obtain ⟨hout, hcut⟩ := ReplayInputs125.view_fixes_output_and_cut rootH rootS avOf earlyOf msgH msgS body mt H U hv
      have ho : (((A).search mt).run H).1 = (A).proof mt U := ((A).proof_eq mt H).symm.trans hout.symm
      have hsig : sigma U = sigma H := by unfold hashSig sideCtx; rw [hout, hcut]
      dsimp only
      rw [ho, ← hsig]
      intro lift hp hc hseen hpath
      have ht := ReplayInputs125.tape_eq rootH rootS avOf earlyOf msgH msgS body mt U
      change accepts Hash (sigma U) (msgH ((A).proof mt U))
        (roleTape (ReplayInputs125.points rootH rootS avOf earlyOf msgH ((A).proof mt U)) U) lift at hp
      rw [ht] at hp
      change Compatible lift ((Hash.Vc (sigma U).2.1 (sigma U).2.2).decodeQuery
        (roleTape (ReplayInputs125.points rootH rootS avOf earlyOf msgH ((A).proof mt U)) U qryIdx)) _ at hc
      rw [ht] at hc
      have hseen' : embed (msgPoint (ctx ((A).proof mt U)) msgH ((A).proof mt U) 0) ∈ queried ((A).search mt) U := by
        have hrun : ((A).search mt).run U = ((A).search mt).run H := congrArg Prod.fst hv
        unfold queried
        rw [hrun]
        exact hseen
      rcases canonical_completion Hash body rootH rootS avOf earlyOf msgH msgS mt represent hashPublic wire U lift
          hp hc (hwmsgs _ _) hseen' hpath with h | h | h
      · exact ⟨3, h⟩
      · exact ⟨4, h⟩
      · exact ⟨5, h⟩

end Count

end LfzkV1.V7FixedTape125
