import LfzkV1.MerkleWork125V7
import LfzkV1.V7FixedTape125
import LfzkV1.SignatureResponseCount125

/-! The v7 two-field knowledge soundness bound for all four hash profiles.

This is the annotated v1 ideal prefix-oracle model for one fixed initial
application transcript. The prover output carries opening sets and the
MAC multiplier annotation. The sample space pairs a uniform Merkle tape with an
independent uniform table at the registered message-prefix and key addresses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace LfzkV1.V7Soundness125

open Finset Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
open LfzkV1.CertifiedV1 LfzkV1.CompiledZk LfzkV1.CompiledZkDeployedHash
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig slice1 slice2)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField
open LfzkV1.NizkAdaptiveTwoField (SideCtx check2)
open LfzkV1.SoundnessAudit LfzkV1.TwoFieldCover125 LfzkV1.TwoFieldV1Rows
open LfzkV1.MacSep LfzkV1.MerkleWork125
open LfzkV1.V7FixedTape125 (HashRoleAt HashPrefixAt HashResponseAt)
open LfzkV1.HashCircuitReplay125 LfzkV1.SignatureResponse125
open LfzkV1.CompiledLongfellow (qryIdx)
open scoped Classical

variable {C D Enc Early HashPublic SigPublic SaltH SaltS Fmac Fh Fs MsgH MsgS Out : Type}
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable [Fintype Early] [DecidableEq Early] [Nonempty HashPublic] [DecidableEq Out]
variable [Inhabited SaltH] [Inhabited SaltS]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable [Field Fh] [Fintype Fh] [DecidableEq Fh] [SumcheckV1Interp Fh]
variable [Field Fs] [Fintype Fs] [DecidableEq Fs] [SumcheckV1Interp Fs]
variable [Fintype MsgH] [DecidableEq MsgH] [Inhabited MsgH]
variable [Fintype MsgS] [DecidableEq MsgS] [Inhabited MsgS]
variable {Mh Ms nth nts nlinh nlins nblk tA N TM : ℕ} {i : Fin 4}
variable {hH : (v7HashRow i).Valid} {hrH : 0 < (v7HashRow i).params.row.openings}
variable {hS : v7SigHahn.Valid}
variable {codecH : Codec SaltH (Col Fh (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {codecS : Codec SaltS (Col Fs v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {decH : RoleDecoders codecH} {decS : RoleDecoders codecS}

variable (Hash : CircuitSide (v7HashRow i) hH hrH (v7HashLogv i)
  C Fh MsgH Mh nth nlinh HashPublic decH Prod.fst)
variable (Signature : CircuitSide v7SigHahn hS v7SigHahn_openings_pos 8
  C Fs MsgS Ms nts nlins SigPublic decS Prod.snd)
variable (body : TwoOracleTree Enc D
  (SignatureBudget125.PairPoint D Fmac Early MsgH MsgS (v7HashRow i)) C Out tA N)
variable (rootH rootS : Out → D) (avOf : Out → Fmac) (earlyOf : Out → Early)
variable (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → MsgS)
variable (claimH : Out → OpeningClaim (v7HashRow i).params.row.n SaltH
    (Col Fh (v7HashRow i).params.nw (v7HashRow i).params.nq) D)
variable (claimS : Out → OpeningClaim v7SigHahn.params.row.n SaltS
    (Col Fs v7SigHahn.params.nw v7SigHahn.params.nq) D)
variable (represent : Fmac → C) (hashPublic : Early → HashPublic) (sigPublic : Out → SigPublic)
variable (d : ExactDecoder C Fmac)
variable (commonH shareH : (Fin Hash.c.ninp → Fh) → Fin nblk → Fmac)
variable (commonS shareS : (Fin Signature.c.ninp → Fs) → Fin nblk → Fmac)
variable (shift : Cut D Enc → Fmac) (tagOf : Out → Fin nblk → Fmac)

local notation "R" => v7HashRow i
local notation "Pt" => SignatureBudget125.PairPoint D Fmac Early MsgH MsgS (v7HashRow i)
local notation "HashRole" => HashRoleAt i
local notation "Prefix" => HashPrefixAt i D Fmac Early MsgH
local notation "Response" => HashResponseAt i Fh
local notation "A" => setup2 body rootH rootS avOf earlyOf msgH msgS
local notation "check" => check2 codecH claimH codecS claimS
local notation "hashPubOf" => hashPublic ∘ earlyOf

local notation "hashCtx" =>
  V7FixedTape125.hashSig body rootH rootS avOf earlyOf msgH msgS
local notation "hashTapeAt" => V7FixedTape125.hashTape body rootH rootS avOf earlyOf msgH msgS
local notation "sigCtx" => sideCtx (A) (represent ∘ avOf) sigPublic

/-- Recover the pair from the Merkle cut and the submitted proof's replay.
Both returned assignments pass their circuit checks and agree on the
common blocks. -/
noncomputable def extractFromTrace (κ : Cut D Enc) (out : Out)
    (tape : Fin (1 + Rounds.Role.length (R).params.nl (R).params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) → C) :
    Option ((Fin Hash.c.ninp → Fh) × (Fin Signature.c.ninp → Fs)) := do
  let key := represent (avOf out)
  let a ← responseWitness Hash (κ, key, hashPubOf out) (msgH out) (slice1 (R) v7SigHahn tape)
  let b ← signatureResponseWitness Signature (κ, key, sigPublic out) (msgS out)
    (slice2 (R) v7SigHahn tape)
  if commonH a = commonS b then some (a, b) else none

noncomputable def extract (mt : Fin TM → D) (H : Pt → C) :
    Option ((Fin Hash.c.ninp → Fh) × (Fin Signature.c.ninp → Fs)) :=
  extractFromTrace Hash Signature avOf earlyOf msgH msgS represent hashPublic sigPublic commonH commonS
    ((A).context mt H) ((A).proof mt H) ((A).challenges mt H)

omit [Nonempty C] [DecidableEq C] [Fintype D] [Fintype Early] [DecidableEq Early]
  [Nonempty HashPublic] [DecidableEq Out] [Field Fmac] [Fintype Fmac]
  [Fintype MsgH] [DecidableEq MsgH] [Inhabited MsgH] [Fintype MsgS] in
theorem extractFromTrace_valid (κ : Cut D Enc) (out : Out)
    (tape : Fin (1 + Rounds.Role.length (R).params.nl (R).params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) → C)
    (a : Fin Hash.c.ninp → Fh) (b : Fin Signature.c.ninp → Fs)
    (h : extractFromTrace Hash Signature avOf earlyOf msgH msgS represent hashPublic sigPublic
      commonH commonS κ out tape = some (a, b)) :
    Hash.c.Satisfied (Hash.pubIn (represent (avOf out)) (hashPubOf out)) a ∧
    Signature.c.Satisfied (Signature.pubIn (represent (avOf out)) (sigPublic out)) b ∧
    commonH a = commonS b := by
  unfold extractFromTrace at h
  obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, hx, rfl⟩ := responseWitness_good Hash _ _ _ _ ha
  obtain ⟨y, hy, rfl⟩ := signatureResponseWitness_good Signature _ _ _ _ hb
  exact ⟨hx, hy, heq⟩

omit [DecidableEq C] [Fintype D] [Fintype Early] [DecidableEq Early]
  [Nonempty HashPublic] [DecidableEq Out] [Field Fmac] [Fintype Fmac]
  [Fintype MsgH] [DecidableEq MsgH] [Fintype MsgS] in
theorem extract_valid (mt : Fin TM → D) (H : Pt → C)
    (a : Fin Hash.c.ninp → Fh) (b : Fin Signature.c.ninp → Fs)
    (h : extract Hash Signature body rootH rootS avOf earlyOf msgH msgS represent hashPublic sigPublic
      commonH commonS mt H = some (a, b)) :
    let out := (A).proof mt H
    Hash.c.Satisfied (Hash.pubIn (represent (avOf out)) (hashPubOf out)) a ∧
    Signature.c.Satisfied (Signature.pubIn (represent (avOf out)) (sigPublic out)) b ∧
    commonH a = commonS b :=
  extractFromTrace_valid Hash Signature avOf earlyOf msgH msgS represent hashPublic sigPublic commonH commonS
    ((A).context mt H) ((A).proof mt H) ((A).challenges mt H) a b h

/-- Both compiled verifiers accept at the replayed MAC multiplier, and the
query-trace extractor fails to return a matching circuit witness pair. -/
def extractionFailure (mt : Fin TM → D) (H : Pt → C) : Prop :=
  let out := (A).proof mt H
  Hash.toSide.acceptsDH (A) (check) rootH msgH claimH (represent ∘ avOf) hashPubOf (slice1 (R) v7SigHahn) mt H ∧
  Signature.toSide.acceptsDH (A) (check) rootS msgS claimS (represent ∘ avOf) sigPublic (slice2 (R) v7SigHahn) mt H ∧
  d.decode (H ((A).hashInput out 0)) = avOf out ∧
  extract Hash Signature body rootH rootS avOf earlyOf msgH msgS represent hashPublic sigPublic
    commonH commonS mt H = none

private theorem merkleFuel_le (i : Fin 4) :
    2 * v7SigHahn.params.row.n + 2 * (v7HashRow i).params.row.n ≤ 14000 := by
  fin_cases i <;> decide

private theorem verifierFuel_le (i : Fin 4) :
    1 + Rounds.Role.length (v7HashRow i).params.nl (v7HashRow i).params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds ≤ 1200 := by
  fin_cases i <;> decide

private theorem hashColumns_ge (i : Fin 4) : 2048 ≤ (v7HashRow i).params.row.n := by
  fin_cases i <;> decide

omit [DecidableEq C] [DecidableEq Early] [Nonempty HashPublic] [DecidableEq Out]
  [Field Fmac] [DecidableEq Fmac] [DecidableEq MsgH] [DecidableEq MsgS] in
private theorem annotated_fs_bound
    (hD : Fintype.card D = 2^256)
    (htape : 2 * v7SigHahn.params.row.n + 2 * (R).params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (inputLength : Enc → ℕ)
    (hleafH : ∀ sm, inputLength (codecH.leafEnc sm) = leafInputBytes (v7HashTableauRows i) 16)
    (hnodeH : ∀ labels, inputLength (codecH.nodeEnc labels) = 64)
    (hleafS : ∀ sm, inputLength (codecS.leafEnc sm) = leafInputBytes 19 32)
    (E : (Fin TM → D) → (Pt → C) → Prop)
    (haccept : ∀ mt H, E mt H →
      Hash.toSide.acceptsDH (A) (check) rootH msgH claimH (represent ∘ avOf) hashPubOf (slice1 (R) v7SigHahn) mt H ∧
      Signature.toSide.acceptsDH (A) (check) rootS msgS claimS (represent ∘ avOf) sigPublic (slice2 (R) v7SigHahn) mt H)
    (hfixed : ∀ mt,
      V7ReplayCharge125.sampleCount (fun H => E mt H ∧ (A).Explains decH Prod.fst claimH mt H ∧
        (A).Explains decS Prod.snd claimS mt H) / Fintype.card (Pt → C) ≤
        (97 + N * (701 / 100)) / 2^128) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) => E ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card Pt) ≤
      (if N + tA = 0 then 33628000 / 2^256 else (N + tA : ℚ) / 2^125) := by
  classical
  let left := check2LeftReplay codecH decH claimH codecS claimS (Key := D × D) Prod.fst
  let right := check2RightReplay codecH claimH codecS decS claimS (Key := D × D) Prod.snd
  have hReplayPos : 0 < 1 + Rounds.Role.length (R).params.nl (R).params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds := by omega
  refine SoundnessCompose125.ratio_le_of_fixed_merkle (A) left right E
    (merkleFuel_le i) (verifierFuel_le i) hReplayPos htape hTM hD (hashColumns_ge i)
    ?_ ?_ ?_ ?_ inputLength (leafInputBytes (v7HashTableauRows i) 16) (leafInputBytes 19 32) 64
    (v7Hash_leaf_input_disjoint i).1.symm (by decide) hleafH hnodeH hleafS ?_
  · intro mt H he
    exact Hash.toSide.acceptsDH_merkle (A) (check) rootH (fun _ => rfl)
      msgH claimH (represent ∘ avOf) hashPubOf (slice1 (R) v7SigHahn) mt H (haccept mt H he).1
  · intro mt H he
    exact Signature.toSide.acceptsDH_merkle (A) (check) rootS (fun _ => rfl)
      msgS claimS (represent ∘ avOf) sigPublic (slice2 (R) v7SigHahn) mt H (haccept mt H he).2
  · intro mt H he
    exact SoundnessCompose125.opening_nonempty_of_acceptsDH Hash.toSide (A) (check)
      rootH msgH claimH (represent ∘ avOf) hashPubOf (slice1 (R) v7SigHahn) mt H (haccept mt H he).1
  · intro mt H he
    exact SoundnessCompose125.opening_nonempty_of_acceptsDH Signature.toSide (A) (check)
      rootS msgS claimS (represent ∘ avOf) sigPublic (slice2 (R) v7SigHahn) mt H (haccept mt H he).2
  · intro _ mt
    convert hfixed mt using 2
    apply congrArg (fun s : Finset (Pt → C) => (s.card : ℚ))
    ext H
    simp [left, right, check2LeftReplay, check2RightReplay]

set_option maxHeartbeats 3000000 in
/-- Work-normalized knowledge soundness for the four registered v7
profiles in the annotated v1 ideal prefix-oracle model. The extractor
receives the adversary's Merkle trace and the actual verifier responses. -/
theorem annotated_fs_knowledge_soundness_125 {Wire : Type} [Fintype Wire]
    (hD : Fintype.card D = 2^256) (hmacCard : Fintype.card Fmac = 2^128)
    (htape : 2 * v7SigHahn.params.row.n + 2 * (R).params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (inputLength : Enc → ℕ)
    (hleafH : ∀ sm, inputLength (codecH.leafEnc sm) = leafInputBytes (v7HashTableauRows i) 16)
    (hnodeH : ∀ labels, inputLength (codecH.nodeEnc labels) = 64)
    (hleafS : ∀ sm, inputLength (codecS.leafEnc sm) = leafInputBytes 19 32)
    (sigPubAt : SignaturePoint D Fmac Early MsgH MsgS (v7HashRow i) → SigPublic)
    (hsigPub : ∀ out (j : Fin (Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds)),
      sigPubAt (msgPoint (ctxOf rootH rootS avOf earlyOf out, fun k => msgH out k.val) msgS out j.val) =
        sigPublic out)
    (wire : ∀ s : Sig D C HashPublic Enc,
      CanonicalHashPrefix125.FieldMessages ((HashCut125.side Hash).V s)
        (v7HashRow i).params.nl (v7HashRow i).params.rounds)
    (toResponse : Wire ↪ Response) (wireResponse : Out → Wire)
    (encode : Prefix → Wire → MsgH) (decode : Prefix → MsgH → Option Wire)
    (valid : Prefix → MsgH → Prop)
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
    (hrowSatH : ∀ (mt : Fin TM → D) (H : Pt → C) a,
      let out := (A).proof mt H
      Hash.c.Satisfied (Hash.pubIn (represent (avOf out)) (hashPubOf out)) a →
      shiftTag (shift ((A).context mt H) + avOf out) (shareH a) (commonH a) = tagOf out)
    (hrowSatS : ∀ (mt : Fin TM → D) (H : Pt → C) a,
      let out := (A).proof mt H
      Signature.c.Satisfied (Signature.pubIn (represent (avOf out)) (sigPublic out)) a →
      shiftTag (shift ((A).context mt H) + avOf out) (shareS a) (commonS a) = tagOf out) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      extractionFailure Hash Signature body rootH rootS avOf earlyOf msgH msgS claimH claimS
        represent hashPublic sigPublic d commonH commonS ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card Pt) ≤
      (if N + tA = 0 then 33628000 / 2^256 else (N + tA : ℚ) / 2^125) := by
  classical
  let E : (Fin TM → D) → (Pt → C) → Prop :=
    extractionFailure Hash Signature body rootH rootS avOf earlyOf msgH msgS claimH claimS
      represent hashPublic sigPublic d commonH commonS
  refine annotated_fs_bound Hash Signature body rootH rootS avOf earlyOf msgH msgS claimH claimS
    represent hashPublic sigPublic hD htape hTM inputLength hleafH hnodeH hleafS E
    (fun _ _ h => ⟨h.1, h.2.1⟩) ?_
  intro mt
  let explained (H : Pt → C) :=
    E mt H ∧ (A).Explains decH Prod.fst claimH mt H ∧ (A).Explains decS Prod.snd claimS mt H
  let ss (H : Pt → C) := signatureResponseWitness Signature (sigCtx mt H) (msgS ((A).proof mt H))
    (slice2 (R) v7SigHahn ((A).challenges mt H))
  let sig (H : Pt → C) :=
    Signature.toSide.acceptsDH (A) (check) rootS msgS claimS
      (represent ∘ avOf) sigPublic (slice2 (R) v7SigHahn) mt H ∧
    (A).Explains decS Prod.snd claimS mt H ∧ ss H = none
  refine V7FixedTape125.fixed_tape_cover_bound Hash Signature body rootH rootS avOf earlyOf msgH msgS mt
    represent hashPublic d commonH shareH commonS shareS shift wire
    toResponse wireResponse encode decode valid hdecode hvalid hwire hwmsgs hwresp hmacCard explained sig ?_ ?_
  · exact signature_response_failure_count_le Signature represent sigPubAt body (check) rootH rootS avOf earlyOf
      sigPublic msgH msgS hsigPub claimS mt sig (fun _ h => h.2.2) (fun _ h => h.1) (fun _ h => h.2.1)
  · intro H h hnSig hnMac hnTerm hnAmbig
    obtain ⟨⟨ha, hb, hk, hnone⟩, hx, hy⟩ := h
    let out := (A).proof mt H
    let k := (A).context mt H
    let s := hashCtx mt represent hashPublic H
    let t := hashTapeAt mt H
    cases hs : ss H with
    | none => exact (hnSig ⟨hb, hy, hs⟩).elim
    | some b =>
      obtain ⟨sys, hbuild, hterminal⟩ :=
        terminal_cover_of_acceptsDH Hash (A) (check) rootH (fun _ => rfl) msgH claimH
          (represent ∘ avOf) hashPubOf (slice1 (R) v7SigHahn) mt H ha hx
      rcases hterminal with hterm | hamb | ⟨lift, hpass, hcomp, hhigh, huniq⟩
      · exact (hnTerm ⟨sys, hbuild, hterm⟩).elim
      · exact (hnAmbig hamb).elim
      refine ⟨lift, ?_, hpass, hcomp, huniq⟩
      intro hsat
      let a := (HashCut125.side Hash).wit s lift
      have hda : responseLift Hash s (msgH out) t = some lift :=
        responseLift_eq_some Hash s (msgH out) t sys lift hhigh
      have hra : responseWitness Hash s (msgH out) t = some a := by
        unfold responseWitness
        rw [hda]
        change (if (HashCut125.side Hash).Sat s lift then some a else none) = some a
        exact if_pos hsat
      have hga : (HashCut125.side Hash).Good s a := ⟨lift, hsat, rfl⟩
      have hgb := signatureResponseWitness_good Signature (sigCtx mt H) (msgS out)
        (slice2 (R) v7SigHahn ((A).challenges mt H)) b hs
      have hne : commonS b ≠ commonH a := by
        intro heq
        have he : extract Hash Signature body rootH rootS avOf earlyOf msgH msgS represent hashPublic
            sigPublic commonH commonS mt H = some (a, b) := by
          unfold extract extractFromTrace
          change (responseWitness Hash s (msgH out) t).bind _ = _
          rw [hra]
          change (ss H).bind _ = _
          rw [hs]
          change (if commonH a = commonS b then some (a, b) else none) = some (a, b)
          exact if_pos heq.symm
        have hc := he.symm.trans hnone
        cases hc
      have hmac := MacCharge125.v7_bad_key_of_sides Signature Hash k (represent (avOf out))
        (represent (avOf out)) (sigPublic out) (hashPubOf out)
        commonS shareS commonH shareH b a hgb hga hne (shift k) (avOf out)
        d (H ((A).hashInput out 0)) hk (tagOf out)
        (hrowSatS mt H b (Signature.toSide_good_property
          (fun s w => Signature.c.Satisfied (Signature.pubIn s.2.1 s.2.2) w)
          (fun _ _ hw => hw) (sigCtx mt H) b hgb))
        (hrowSatH mt H a hsat)
      exact hnMac hmac

end LfzkV1.V7Soundness125
