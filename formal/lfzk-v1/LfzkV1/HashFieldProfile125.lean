import LfzkV1.HashFieldPoint125
import LfzkV1.CanonicalSecondary125
import LfzkV1.HashCut125
import LfzkV1.LiftOpening125

/-! The v7 hash-side field charges at the registered transcript schedule. -/

set_option autoImplicit false

namespace LfzkV1.HashFieldProfile125

open Finset LigeroFamily Merkle.MH RbrLongfellow
open Bcs.TotalOracle (AgreeOff)
open LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.CompiledZk LfzkV1.RbrZkLongfellow
open LfzkV1.RbrZkSplit LfzkV1.NizkDeployedHash LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open scoped Classical

section Schedule

variable {C F X Q Msg Lift Ctx : Type} [Field F] [Fintype F] [SumcheckV1Interp F] [Inhabited Msg]
  {c : QuadCircuit F} {M L logv : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0}
  {H : ZkHonest F Lift L 0} {asg : Lift → LigeroAssignment c.ninp M F} {Sat : Lift → Prop}

/-- Use a boundary and query at the registered layer count, identified with
the circuit's own layer count by the profile. -/
private def badAt {nl : ℕ} (hnl : c.nl = nl) (B : ZkBoundary V H asg nl w)
    (primary : Option Lift) (p : MPoint Ctx Msg nl w) (pref : Fin p.role.slot → C) (coin : C) : Prop := by
  subst nl
  exact HashFieldPoint125.bad (Sat := Sat) B primary p pref coin

section Counting

variable [Fintype C] [DecidableEq F] [Fintype Lift]
  [DecidableEq X] [Fintype X] [Fintype Q] [DecidableEq Q]

private theorem badAt_sum_le [Nonempty C] {pub : Fin c.ninp → F} {nl : ℕ}
    (hnl : c.nl = nl) (hpos : 0 < c.nl) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (hlist : Fintype.card Lift ≤ 2)
    (hq : Fintype.card F = 2^128) (primary : Option Lift)
    (p : MPoint Ctx Msg nl w) (pref : Fin p.role.slot → C) :
    (∑ coin : C, if badAt (Sat := Sat) hnl FD.B primary p pref coin then (1 : ℚ) else 0) ≤
      Fintype.card C * ((if p.role.slot = 0 then 7 else 4) / 2^128) := by
  subst nl
  exact HashFieldPoint125.bad_sum_le hpos hV hst0 FD hexact hlogv hlist hq primary p pref

omit [Fintype Lift] in
private theorem initialEscapeAt_sum_le {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (hF : Fintype.card F = 2 ^ 128)
    (lift : Lift) :
    (∑ coin : C,
      if ¬ Sat lift ∧ (∀ j, ¬ H.Pend lift j []) ∧
          H.sum lift 0 (V.st0 (V.decodeInit coin).1) (V.decodeInit coin).2.1
            (V.decodeInit coin).2.2 [] = 0
      then (1 : ℚ) else 0) ≤ Fintype.card C * (7 / 2^128) := by
  subst nl
  let msgs : ℕ → Msg := fun _ => default
  have h := HashFieldPoint125.initial_escape_sum_le FD hexact hlogv hF msgs ⟨0, hpos⟩ rfl lift
  simp only [HashFieldCharge125.initial_escapes_iff msgs ⟨0, hpos⟩ rfl lift] at h
  exact h

end Counting

variable [DecidableEq F]

/-- Run the registered verifier points in role order. -/
noncomputable def pointTape {nl : ℕ} (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C)
    (msgs : ℕ → Msg) : Fin (Rounds.Role.length nl w) → C :=
  fun k => oracle (msgPoint ctx (fun ms j => ms j) msgs k.val)

private def secondaryAt {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    (B : ZkBoundary V H asg nl w) (primary : Option Lift)
    (msgs : ℕ → Msg) (tape : Fin (Rounds.Role.length nl w) → C) (lift : Lift) : Prop := by
  subst nl
  let init : Rounds.Role c.nl w := .layerPair ⟨0, hpos⟩
  exact primary ≠ some lift ∧
    HashFieldCharge125.escapes (V := V) (H := H) (asg := asg) (Sat := Sat)
      msgs init lift .start (tape init.index) ∧
    HashFieldPath125.CanonicalRun V msgs B lift tape

private theorem bad_or_secondary_at {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    {pub : Fin c.ninp → F} (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (B : ZkBoundary V H asg nl w) (primary : Option Lift)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C)
    (msgs : ℕ → Msg) (lift : Lift) (hfalse : ¬ Sat lift)
    (sys : LigeroSystem c.ninp M F)
    (hBuilt : zkBuilt (nl := nl) (w := w) V msgs (pointTape ctx oracle msgs) = some sys)
    (hsat : sys.Sat (asg lift).1 (asg lift).2) :
    (∃ j : Fin (Rounds.Role.length nl w), let p := msgPoint ctx (fun ms k => ms k) msgs j.val
      badAt (Sat := Sat) hnl B primary p (mpoints.chal oracle p) (oracle p)) ∨
      secondaryAt (Sat := Sat) hnl hpos B primary msgs (pointTape ctx oracle msgs) lift := by
  subst nl
  rcases HashFieldCharge125.selected_field_path V hpos hV hst0 B primary msgs
    (pointTape ctx oracle msgs) lift hfalse sys hBuilt hsat with h | h | h
  · obtain ⟨role, hposRole, hfield, hb⟩ := h
    exact Or.inl ⟨role.index, HashFieldPoint125.bad_of_later_run B primary ctx oracle msgs role
      lift hposRole hfield hb⟩
  · let role : Rounds.Role c.nl w := .layerPair ⟨0, hpos⟩
    have hslot : role.slot = 0 := by simp [role, Rounds.Role.slot, Rounds.Role.layerBase]
    have hinit : (Rounds.Role.layerPair (w := w) ⟨0, hpos⟩).index.val = 0 := hslot
    have hb := HashFieldPoint125.bad_of_primary_run B primary ctx oracle msgs ⟨0, hpos⟩ rfl
      lift h.1 (by simpa only [pointTape, hinit] using h.2)
    refine Or.inl ⟨⟨0, by rw [← hslot]; exact role.slot_lt⟩, hb⟩
  · exact Or.inr h

omit [DecidableEq F] in
private theorem badAt_fieldSlot {nl : ℕ} (hnl : c.nl = nl)
    (B : ZkBoundary V H asg nl w)
    (primary : Option Lift) (p : MPoint Ctx Msg nl w) (pref : Fin p.role.slot → C)
    (coin : C) (h : badAt (Sat := Sat) hnl B primary p pref coin) :
    p.role.slot < Rounds.Role.layerBase w nl + 1 := by
  subst nl
  by_contra hslot
  have hzero : p.role.slot ≠ 0 := by omega
  simp only [badAt, HashFieldPoint125.bad, if_neg hzero, if_neg hslot] at h

omit [Inhabited Msg] in
private theorem secondaryAt_initial {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    (B : ZkBoundary V H asg nl w)
    (primary : Option Lift) (msgs : ℕ → Msg) (tape : Fin (Rounds.Role.length nl w) → C)
    (lift : Lift) (h : secondaryAt (Sat := Sat) hnl hpos B primary msgs tape lift) :
    primary ≠ some lift ∧ ¬ Sat lift ∧ (∀ j, ¬ H.Pend lift j []) ∧
      let coin := tape ⟨0, by
        have h : 0 < Rounds.Role.length nl w := by simp [Rounds.Role.length]
        exact h⟩
      let draw := V.decodeInit coin
      H.sum lift 0 (V.st0 draw.1) draw.2.1 draw.2.2 [] = 0 := by
  subst nl
  exact ⟨h.1, (HashFieldCharge125.initial_escapes_iff msgs ⟨0, hpos⟩ rfl lift _).mp h.2.1⟩

private theorem canonical_prefix_eq_at {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    {pub : Fin c.ninp → F} (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (B : ZkBoundary V H asg nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : B.W = zkWP pub wOf) (primary : Option Lift)
    (wire : CanonicalHashPrefix125.FieldMessages V nl w)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C) (lift : Lift) (a b : ℕ → Msg)
    (ha : ∀ role : Rounds.Role nl w, wire.valid role (a role.slot))
    (hb : ∀ role : Rounds.Role nl w, wire.valid role (b role.slot))
    (ca : secondaryAt (Sat := Sat) hnl hpos B primary a (pointTape ctx oracle a) lift)
    (cb : secondaryAt (Sat := Sat) hnl hpos B primary b (pointTape ctx oracle b) lift) :
    ∀ j < (Rounds.Role.ligeroQuery : Rounds.Role nl w).slot, a j = b j := by
  subst nl
  exact CanonicalHashPrefix125.canonical_prefix_eq hpos hV hst0 B wOf hW wire ctx oracle lift a b
    ha hb ca.2.2 cb.2.2

private def eligibleAt {nl : ℕ} (hnl : c.nl = nl) (B : ZkBoundary V H asg nl w)
    (wire : CanonicalHashPrefix125.FieldMessages V nl w) (primary : Option Lift)
    (reply : Lift → Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C)
    (initial opening : MPoint Ctx Msg nl w) : Prop := by
  subst nl
  exact CanonicalSecondary125.eligible B wire (fun lift => primary ≠ some lift)
    reply ctx oracle initial opening

omit [DecidableEq F] in
private theorem eligibleAt_of_secondaryAt {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    (B : ZkBoundary V H asg nl w)
    (wire : CanonicalHashPrefix125.FieldMessages V nl w) (primary : Option Lift)
    (reply : Lift → Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C) (lift : Lift) (msgs : ℕ → Msg)
    (hmsg : ∀ role : Rounds.Role nl w, wire.valid role (msgs role.slot))
    (hsec : secondaryAt (Sat := Sat) hnl hpos B primary msgs (pointTape ctx oracle msgs) lift)
    (hreply : reply lift (zkBuilt (w := w) V msgs (pointTape ctx oracle msgs))
      (V.decodeChal (pointTape ctx oracle msgs (Rounds.Role.ligeroChallenge : Rounds.Role nl w).index))
      (msgs (Rounds.Role.ligeroQuery : Rounds.Role nl w).slot)) :
    eligibleAt hnl B wire primary reply ctx oracle (msgPoint ctx (fun ms j => ms j) msgs 0)
      (msgPoint ctx (fun ms j => ms j) msgs (Rounds.Role.ligeroQuery : Rounds.Role nl w).slot) := by
  subst nl
  exact ⟨lift, hsec.1, msgs, hmsg, hsec.2.2, hreply, rfl, rfl⟩

private theorem eligibleAt_unique {nl : ℕ} (hnl : c.nl = nl) (hpos : 0 < c.nl)
    {pub : Fin c.ninp → F} (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (B : ZkBoundary V H asg nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : B.W = zkWP pub wOf) (primary : Option Lift)
    (wire : CanonicalHashPrefix125.FieldMessages V nl w)
    (hsecondary : ∀ a b, primary ≠ some a → primary ≠ some b → a = b)
    (reply : Lift → Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (hreply : ∀ lift, primary ≠ some lift → ∀ sys x {a b},
      reply lift sys x a → reply lift sys x b → a = b)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C)
    (initial a b : MPoint Ctx Msg nl w)
    (ha : eligibleAt hnl B wire primary reply ctx oracle initial a)
    (hb : eligibleAt hnl B wire primary reply ctx oracle initial b) : a = b := by
  subst nl
  exact CanonicalSecondary125.eligible_unique hpos hV hst0 B wOf hW wire
    (fun lift => primary ≠ some lift) hsecondary reply hreply ctx oracle initial a b ha hb

omit [DecidableEq F] in
private theorem eligibleAt_off_opening {nl : ℕ} (hnl : c.nl = nl)
    (B : ZkBoundary V H asg nl w) (wire : CanonicalHashPrefix125.FieldMessages V nl w)
    (primary : Option Lift)
    (reply : Lift → Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (ctx : Ctx) (initial opening target : MPoint Ctx Msg nl w)
    (ht : target.role = .ligeroQuery) {oracle oracle' : MPoint Ctx Msg nl w → C}
    (hoff : AgreeOff target oracle oracle') :
    eligibleAt hnl B wire primary reply ctx oracle initial opening ↔
      eligibleAt hnl B wire primary reply ctx oracle' initial opening := by
  subst nl
  exact CanonicalSecondary125.eligible_off_opening B wire (fun lift => primary ≠ some lift)
    reply ctx initial opening target ht hoff

omit [DecidableEq F] in
private theorem eligibleAt_reply_at {nl : ℕ} (hnl : c.nl = nl)
    (B : ZkBoundary V H asg nl w) (wire : CanonicalHashPrefix125.FieldMessages V nl w)
    (primary : Option Lift)
    (reply : Lift → Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (ctx : Ctx) (oracle : MPoint Ctx Msg nl w → C)
    (initial opening : MPoint Ctx Msg nl w)
    (h : eligibleAt hnl B wire primary reply ctx oracle initial opening) :
    ∃ lift, primary ≠ some lift ∧ ∃ msgs : ℕ → Msg,
      reply lift (zkBuilt (w := w) V msgs (pointTape ctx oracle msgs))
        (V.decodeChal (pointTape ctx oracle msgs (Rounds.Role.ligeroChallenge : Rounds.Role nl w).index))
        (msgs (Rounds.Role.ligeroQuery : Rounds.Role nl w).slot) ∧
      opening = msgPoint ctx (fun ms j => ms j) msgs (Rounds.Role.ligeroQuery : Rounds.Role nl w).slot := by
  subst nl
  obtain ⟨lift, hsec, msgs, _, _, hr, _, hopen⟩ := h
  exact ⟨lift, hsec, msgs, hr, hopen⟩

end Schedule

section Profile

variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] {M nt nlin : ℕ}
variable {Enc D Salt X : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {i : Fin 4} {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (S : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey)

local notation "R" => v7HashRow i
local notation "Lift" => sideLiftAt S (HashCut125.radius i)
local notation "Side" => HashCut125.side S
local notation "Point" => MPoint


/-- The primary lift is the fixed cut's largest agreement set. Neither the
key answer nor the point's transcript prefix enters the tie breaking. -/
noncomputable def primary (σ : Sig D C X Enc) : Option (Lift σ) :=
  LiftOpening125.primary ((R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
    (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
      (rootOfKey σ.1.1, σ.1.2)) (HashCut125.radius i)

/-- The primary lift is literally the same object at two public contexts
sharing the paired commitment cut. -/
theorem primary_eq_of_same_cut (κ : (D × D) × List (Enc × D))
    (key key' : C) (pub pub' : X) :
    primary S (κ, key, pub) = primary S (κ, key', pub') := rfl

variable [Inhabited Msg]

/-- The actual field predicate at a deployed hash oracle input. It uses
the enlarged-radius side's field data, assignment and pending checks. -/
def bad {Ctx : Type} (σ : Sig D C X Enc) (p : Point Ctx Msg (R).params.nl (R).params.rounds)
    (pref : Fin p.role.slot → C) (coin : C) : Prop :=
  badAt (Sat := (Side).Sat σ) S.hnl ((Side).FD σ).B (primary S σ) p pref coin

omit [Inhabited Msg] in
private theorem depth_pos : 0 < S.c.nl := by
  rw [S.hnl]
  fin_cases i <;> decide

private theorem profile_field_card (j : Fin 4) : (v7HashRow j).params.row.fieldSize = 2^128 := by
  fin_cases j <;> rfl

/-- Each real field query pays at most seven errors for the initial draw
and four for every later draw, uniformly in the raw answer alphabet. -/
theorem bad_sum_le [Nonempty C] {Ctx : Type} (σ : Sig D C X Enc)
    (p : Point Ctx Msg (R).params.nl (R).params.rounds) (pref : Fin p.role.slot → C) :
    (∑ coin : C, if bad S σ p pref coin then (1 : ℚ) else 0) ≤
      Fintype.card C * ((if p.role.slot = 0 then 7 else 4) / 2^128) := by
  have hv : v7HashLogv i ≤ 5 := by fin_cases i <;> decide
  have hc : Fintype.card (Lift σ) ≤ 2 := by
    have h := HashCut125.side_lift_card_le S σ
    rwa [HashCut125.row_candidate_count] at h
  have hq : Fintype.card F = 2^128 := S.hF.trans (profile_field_card i)
  exact badAt_sum_le S.hnl (depth_pos S) (S.hV _ _) (S.hst0 _ _) ((Side).FD σ)
    ((Side).hexact σ) hv hc hq (primary S σ) p pref

/-- The exceptional canonical path of a secondary lift. The initial escape
and the exact canonical field run are both part of this event. -/
def canonicalSecondary (σ : Sig D C X Enc)
    (msgs : ℕ → Msg) (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (lift : Lift σ) : Prop :=
  secondaryAt (Sat := (Side).Sat σ) S.hnl (depth_pos S) ((Side).FD σ).B
    (primary S σ) msgs tape lift

/-- The registered verifier run of a selected circuit-failing lift which
satisfies the built system either hits a deployed field point or witnesses
the secondary canonical branch. -/
theorem bad_or_canonicalSecondary {Ctx : Type} (σ : Sig D C X Enc)
    (ctx : Ctx) (oracle : Point Ctx Msg (R).params.nl (R).params.rounds → C)
    (msgs : ℕ → Msg) (lift : Lift σ) (hfalse : ¬ (Side).Sat σ lift)
    (sys : LigeroSystem S.c.ninp M F)
    (hBuilt : zkBuilt (nl := (R).params.nl) (w := (R).params.rounds) ((Side).V σ) msgs
      (pointTape ctx oracle msgs) = some sys)
    (hsat : sys.Sat ((Side).asg σ lift).1 ((Side).asg σ lift).2) :
    (∃ j : Fin (Rounds.Role.length (R).params.nl (R).params.rounds),
      let p := msgPoint ctx (fun ms k => ms k) msgs j.val
      bad S σ p (mpoints.chal oracle p) (oracle p)) ∨
      canonicalSecondary S σ msgs (pointTape ctx oracle msgs) lift :=
  bad_or_secondary_at S.hnl (depth_pos S) (S.hV _ _) (S.hst0 _ _)
    ((Side).FD σ).B (primary S σ) ctx oracle msgs lift hfalse sys hBuilt hsat

/-- The field predicate has no mass on either Ligero terminal slot. -/
theorem bad_field_slot {Ctx : Type} (σ : Sig D C X Enc)
    (p : Point Ctx Msg (R).params.nl (R).params.rounds)
    (pref : Fin p.role.slot → C) (coin : C) (h : bad S σ p pref coin) :
    p.role.slot < Rounds.Role.layerBase (R).params.rounds (R).params.nl + 1 :=
  badAt_fieldSlot S.hnl ((Side).FD σ).B (primary S σ) p pref coin h

omit [Inhabited Msg] in
/-- The secondary case includes an escape at the grouped initial draw,
and excludes a pending intermediate assertion. -/
theorem canonicalSecondary_init (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (lift : Lift σ) (h : canonicalSecondary S σ msgs tape lift) :
    primary S σ ≠ some lift ∧ ¬ (Side).Sat σ lift ∧ (∀ j, ¬ ((Side).H σ).Pend lift j []) ∧
      let coin := tape ⟨0, by simp [Rounds.Role.length]⟩
      let draw := ((Side).V σ).decodeInit coin
      ((Side).H σ).sum lift 0 (((Side).V σ).st0 draw.1) draw.2.1 draw.2.2 [] = 0 :=
  secondaryAt_initial S.hnl (depth_pos S) ((Side).FD σ).B (primary S σ) msgs tape lift h

/-- For one secondary lift and one oracle, the registered field transcript
before the opening point is unique under the serialized-field discipline. -/
theorem canonicalSecondary_prefix_eq {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (ctx : Ctx) (oracle : Point Ctx Msg (R).params.nl (R).params.rounds → C)
    (lift : Lift σ) (a b : ℕ → Msg)
    (ha : ∀ role : Rounds.Role (R).params.nl (R).params.rounds, wire.valid role (a role.slot))
    (hb : ∀ role : Rounds.Role (R).params.nl (R).params.rounds, wire.valid role (b role.slot))
    (ca : canonicalSecondary S σ a (pointTape ctx oracle a) lift)
    (cb : canonicalSecondary S σ b (pointTape ctx oracle b) lift) :
    ∀ j < (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot, a j = b j :=
  canonical_prefix_eq_at S.hnl (depth_pos S) (S.hV _ _) (S.hst0 _ _) ((Side).FD σ).B
    (fun ℓ => ((Side).asg σ ℓ).1) rfl (primary S σ) wire ctx oracle lift a b ha hb ca cb

omit [Inhabited Msg] in
/-- The two-element lift list leaves at most one secondary candidate. -/
theorem secondary_unique (σ : Sig D C X Enc) (a b : Lift σ)
    (ha : primary S σ ≠ some a) (hb : primary S σ ≠ some b) : a = b := by
  have hcard := HashCut125.side_lift_card_le S σ
  rw [HashCut125.row_candidate_count] at hcard
  exact LiftOpening125.secondary_unique hcard ha hb

open LfzkV1.ZkLigeroV1 (Chal)

abbrev HashPoint (i : Fin 4) (Ctx Msg : Type) :=
  MPoint Ctx Msg (v7HashRow i).params.nl (v7HashRow i).params.rounds
abbrev Reply (σ : Sig D C X Enc) := Lift σ → Option (LigeroSystem S.c.ninp M F) →
  Chal F ((v7HashRow i).params.nw) ((v7HashRow i).params.nq) nlin nt → Msg → Prop

/-- The canonical secondary relation on the actual registered v1 addresses.
The response predicate may inspect the built system and batching challenge,
but has no opening-answer argument. -/
def eligible {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (reply : Reply S σ) (ctx : Ctx) (oracle : HashPoint i Ctx Msg → C)
    (initial opening : HashPoint i Ctx Msg) : Prop :=
  eligibleAt S.hnl ((Side).FD σ).B wire (primary S σ) reply ctx oracle initial opening

theorem eligible_of_canonicalSecondary {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (reply : Reply S σ) (ctx : Ctx) (oracle : HashPoint i Ctx Msg → C)
    (lift : Lift σ) (msgs : ℕ → Msg)
    (hmsg : ∀ role : Rounds.Role (R).params.nl (R).params.rounds, wire.valid role (msgs role.slot))
    (hsec : canonicalSecondary S σ msgs (pointTape ctx oracle msgs) lift)
    (hreply : reply lift (zkBuilt (w := (R).params.rounds) ((Side).V σ) msgs (pointTape ctx oracle msgs))
      (((Side).V σ).decodeChal
        (pointTape ctx oracle msgs (Rounds.Role.ligeroChallenge :
          Rounds.Role (R).params.nl (R).params.rounds).index))
      (msgs (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot)) :
    eligible S σ wire reply ctx oracle (msgPoint ctx (fun ms j => ms j) msgs 0)
      (msgPoint ctx (fun ms j => ms j) msgs (Rounds.Role.ligeroQuery :
        Rounds.Role (R).params.nl (R).params.rounds).slot) :=
  eligibleAt_of_secondaryAt S.hnl (depth_pos S) ((Side).FD σ).B wire (primary S σ)
    reply ctx oracle lift msgs hmsg hsec hreply

theorem eligible_unique {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (reply : Reply S σ)
    (hreply : ∀ lift, primary S σ ≠ some lift → ∀ sys x {a b},
      reply lift sys x a → reply lift sys x b → a = b)
    (ctx : Ctx) (oracle : HashPoint i Ctx Msg → C) (initial a b : HashPoint i Ctx Msg)
    (ha : eligible S σ wire reply ctx oracle initial a)
    (hb : eligible S σ wire reply ctx oracle initial b) :
    a = b :=
  eligibleAt_unique S.hnl (depth_pos S) (S.hV _ _) (S.hst0 _ _) ((Side).FD σ).B
    (fun ℓ => ((Side).asg σ ℓ).1) rfl (primary S σ) wire (secondary_unique S σ)
    reply hreply ctx oracle initial a b ha hb

theorem eligible_off_opening {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (reply : Reply S σ) (ctx : Ctx) (initial opening target : HashPoint i Ctx Msg)
    (ht : target.role = .ligeroQuery) {oracle oracle' : HashPoint i Ctx Msg → C}
    (hoff : AgreeOff target oracle oracle') :
    eligible S σ wire reply ctx oracle initial opening ↔
      eligible S σ wire reply ctx oracle' initial opening :=
  eligibleAt_off_opening S.hnl ((Side).FD σ).B wire (primary S σ)
    reply ctx initial opening target ht hoff

/-- The secondary lift's grouped initial escape is read directly from the
initial answer and the context fixed by the commitment cut. -/
def secondaryEscape (σ : Sig D C X Enc) (coin : C) : Prop :=
  ∃ lift : Lift σ, primary S σ ≠ some lift ∧ ¬ (Side).Sat σ lift ∧
    (∀ j, ¬ ((Side).H σ).Pend lift j []) ∧
      let draw := ((Side).V σ).decodeInit coin
      ((Side).H σ).sum lift 0 (((Side).V σ).st0 draw.1) draw.2.1 draw.2.2 [] = 0

omit [Inhabited Msg] in
theorem secondaryEscape_of_canonicalSecondary (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (lift : Lift σ) (h : canonicalSecondary S σ msgs tape lift) :
    secondaryEscape S σ (tape ⟨0, by simp [Rounds.Role.length]⟩) :=
  ⟨lift, canonicalSecondary_init S σ msgs tape lift h⟩

/-- A two-candidate list contains at most one secondary, so its initial
charge has the one-lift seven-error budget. -/
theorem secondaryEscape_sum_le (σ : Sig D C X Enc) :
    (∑ coin : C, if secondaryEscape S σ coin then (1 : ℚ) else 0) ≤
      (Fintype.card C : ℚ) * (7 / 2^128) := by
  by_cases hsec : ∃ lift : Lift σ, primary S σ ≠ some lift
  · obtain ⟨x, hx⟩ := hsec
    have heq (coin : C) : secondaryEscape S σ coin ↔
        ¬ (Side).Sat σ x ∧ (∀ j, ¬ ((Side).H σ).Pend x j []) ∧
          let draw := ((Side).V σ).decodeInit coin
          ((Side).H σ).sum x 0 (((Side).V σ).st0 draw.1) draw.2.1 draw.2.2 [] = 0 := by
      constructor
      · rintro ⟨y, hy, h⟩
        obtain rfl := secondary_unique S σ y x hy hx
        exact h
      · exact fun h => ⟨x, hx, h⟩
    have hv : v7HashLogv i ≤ 5 := by fin_cases i <;> decide
    have hq : Fintype.card F = 2^128 := S.hF.trans (profile_field_card i)
    simpa only [heq] using initialEscapeAt_sum_le S.hnl (depth_pos S) ((Side).FD σ)
      ((Side).hexact σ) hv hq x
  · have hf (coin : C) : ¬ secondaryEscape S σ coin :=
      fun ⟨lift, h, _⟩ => hsec ⟨lift, h⟩
    simp only [hf, if_false, Finset.sum_const_zero]
    positivity

/-- Project the concrete terminal transcript and the lifted-response
predicate from a canonical address. -/
theorem eligible_reply_at {Ctx : Type} (σ : Sig D C X Enc)
    (wire : CanonicalHashPrefix125.FieldMessages ((Side).V σ) (R).params.nl (R).params.rounds)
    (reply : Reply S σ) (ctx : Ctx) (oracle : HashPoint i Ctx Msg → C)
    (initial opening : HashPoint i Ctx Msg)
    (h : eligible S σ wire reply ctx oracle initial opening) :
    ∃ lift : Lift σ, primary S σ ≠ some lift ∧ ∃ msgs : ℕ → Msg,
      reply lift (zkBuilt (w := (R).params.rounds) ((Side).V σ) msgs (pointTape ctx oracle msgs))
        (((Side).V σ).decodeChal
          (pointTape ctx oracle msgs (Rounds.Role.ligeroChallenge :
            Rounds.Role (R).params.nl (R).params.rounds).index))
        (msgs (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot) ∧
      opening = msgPoint ctx (fun ms j => ms j) msgs
        (Rounds.Role.ligeroQuery : Rounds.Role (R).params.nl (R).params.rounds).slot :=
  eligibleAt_reply_at S.hnl ((Side).FD σ).B wire (primary S σ) reply ctx oracle initial opening h

end Profile

end LfzkV1.HashFieldProfile125
