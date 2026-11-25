import LfzkV1.CanonicalHashPrefix125

/-! The secondary lift determines at most one opening input after the
initial field draw. The determination is independent of opening answers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CanonicalSecondary125

open Bcs.TotalOracle
open Finset Merkle.RandomOracle
open LfzkV1.Arith LfzkV1.CanonicalHashPrefix125 LfzkV1.HashFieldPath125
open LfzkV1.RbrZkLongfellow LfzkV1.CompiledZk LfzkV1.NizkDeployedHash
open scoped Classical

variable {C F X Q Msg Lift Ctx : Type} [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] [Inhabited Msg] {c : QuadCircuit F} {w : ℕ → ℕ}
variable {M L logv : ℕ} {code : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0}
variable {honest : ZkHonest F Lift L 0} {assignment : Lift → LigeroAssignment c.ninp M F}

local notation "Role" => Rounds.Role c.nl w
local notation "Point" => MPoint Ctx Msg c.nl w
local notation "System" => LigeroSystem c.ninp M F

/-- A candidate's canonical messages and a high response eligible for that
candidate. Neither part reads the opening answer. -/
def eligible (boundary : ZkBoundary code honest assignment c.nl w)
    (wire : FieldMessages code c.nl w) (secondary : Lift → Prop)
    (reply : Lift → Option System → X → Msg → Prop) (ctx : Ctx)
    (H : Point → C) (initial opening : Point) : Prop :=
  ∃ lift : Lift, secondary lift ∧ ∃ msgs : ℕ → Msg,
    (∀ role : Role, wire.valid role (msgs role.slot)) ∧
    CanonicalRun code msgs boundary lift (runTape ctx H msgs) ∧
    reply lift (zkBuilt (w := w) code msgs (runTape ctx H msgs))
      (code.decodeChal (runTape ctx H msgs (Rounds.Role.ligeroChallenge : Role).index))
      (msgs (Rounds.Role.ligeroQuery : Role).slot) ∧
    initial = msgPoint ctx (fun f i => f i) msgs 0 ∧
    opening = msgPoint ctx (fun f i => f i) msgs (Rounds.Role.ligeroQuery : Role).slot

omit [DecidableEq F] in
theorem eligible_off_opening (boundary : ZkBoundary code honest assignment c.nl w)
    (wire : FieldMessages code c.nl w) (secondary : Lift → Prop)
    (reply : Lift → Option System → X → Msg → Prop) (ctx : Ctx)
    (initial opening target : Point) (ht : target.role = .ligeroQuery)
    {H H' : Point → C} (hoff : AgreeOff target H H') :
    eligible boundary wire secondary reply ctx H initial opening ↔
      eligible boundary wire secondary reply ctx H' initial opening := by
  unfold eligible
  apply exists_congr
  intro lift
  apply and_congr_right
  intro _
  apply exists_congr
  intro msgs
  have hb := built_batch_off_opening (code := code) ctx msgs target ht hoff
  rw [hb.1, hb.2]
  exact and_congr_right fun _ =>
    and_congr_left (fun _ => canonical_run_off_opening boundary lift ctx msgs target ht hoff)

theorem eligible_unique {pub : Fin c.ninp → F} (hpos : 0 < c.nl)
    (hcode : ZkArithProfile.CodeAgreesP c pub L code)
    (hst0 : ∀ G, (code.st0 G).g0 = ZkArithProfile.padG L G ∧
      (code.st0 G).g1 = ZkArithProfile.padG L G)
    (boundary : ZkBoundary code honest assignment c.nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : boundary.W = ZkArithProfile.zkWP pub wOf)
    (wire : FieldMessages code c.nl w) (secondary : Lift → Prop)
    (hsecondary : ∀ a b, secondary a → secondary b → a = b)
    (reply : Lift → Option System → X → Msg → Prop)
    (hreply : ∀ lift, secondary lift → ∀ sys x {a b},
      reply lift sys x a → reply lift sys x b → a = b)
    (ctx : Ctx) (H : Point → C) (initial a b : Point)
    (ha : eligible boundary wire secondary reply ctx H initial a)
    (hb : eligible boundary wire secondary reply ctx H initial b) : a = b := by
  obtain ⟨lift, hs, msgs, hv, hpath, hreplyA, _, rfl⟩ := ha
  obtain ⟨lift', hs', msgs', hv', hpath', hreplyB, _, rfl⟩ := hb
  obtain rfl := hsecondary lift lift' hs hs'
  exact canonical_opening_unique hpos hcode hst0 boundary wOf hW wire ctx H lift
    msgs msgs' hv hv' hpath hpath' (reply lift) (hreply lift hs) hreplyA hreplyB

section OpeningAddress

variable {nl : ℕ} {widths : ℕ → ℕ}

abbrev InitPoint (Ctx Msg : Type) (nl : ℕ) (widths : ℕ → ℕ) :=
  {p : MPoint Ctx Msg nl widths // p.role.slot = 0}

abbrev OpeningPoint (Ctx Msg : Type) (nl : ℕ) (widths : ℕ → ℕ) :=
  {p : MPoint Ctx Msg nl widths // p.role = .ligeroQuery}

noncomputable def initialOf (p : OpeningPoint Ctx Msg nl widths) : InitPoint Ctx Msg nl widths :=
  ⟨mpoints.anc p.val 0, by
    change (LfzkV1.NizkGrinding.roleAt (nl := nl) (w := widths) 0).slot = 0
    exact LfzkV1.NizkGrinding.slot_roleAt (by simp [Rounds.Role.length])⟩

theorem initialOf_eq {ctx : Ctx} {msgs : ℕ → Msg} {p : OpeningPoint Ctx Msg nl widths}
    (hp : p.val = msgPoint ctx (fun f i => f i) msgs (Rounds.Role.ligeroQuery (nl := nl) (w := widths)).slot) :
    (initialOf p).val = msgPoint ctx (fun f i => f i) msgs 0 := by
  change mpoints.anc p.val 0 = _
  rw [hp]
  let role : Rounds.Role nl widths := .ligeroQuery
  have hz : 0 < role.slot := by simp [role, Rounds.Role.slot]
  exact anc_msgPoint ctx (fun f i => f i) msgs hz role.slot_lt

end OpeningAddress

section ParentFirstCount

attribute [local instance 10000] Classical.propDecidable

variable {Pt Init Opening Answer Out : Type} [Fintype Pt] [DecidableEq Pt] [Fintype Init]
  [Fintype Opening] [Fintype Answer] [Nonempty Answer] {N : ℕ}

/-- If the initial draw was observed first, charge the later opening to
that initial draw even when the verifier appends the opening. The small
opening tail multiplies the initial local bound. -/
theorem parent_first_charge_le
    (tree : Tree Pt Answer Out N) (initial : Init → Pt) (opening : Init → Opening → Pt)
    (hne : ∀ p r, opening p r ≠ initial p)
    (eligible : Init → Opening → (Pt → Answer) → Prop)
    (escape : Init → (Pt → Answer) → Answer → Prop)
    (opens : Init → Opening → (Pt → Answer) → Answer → Prop)
    (hunique : ∀ p G r s, eligible p r G → eligible p s G → r = s)
    (heligible : ∀ p r G G', AgreeOff (opening p r) G G' →
      ∀ s, eligible p s G ↔ eligible p s G')
    (hescapeInit : ∀ p G G', AgreeOff (initial p) G G' →
      ∀ a, escape p G a ↔ escape p G' a)
    (hescapeOpen : ∀ p r G G', AgreeOff (opening p r) G G' →
      ∀ a, escape p G a ↔ escape p G' a)
    (hopens : ∀ p r G G', AgreeOff (opening p r) G G' → eligible p r G →
      ∀ b, opens p r G b ↔ opens p r G' b)
    (η ρ : ℚ) (hρ : 0 ≤ ρ)
    (hinit : ∀ p G, ∑ a : Answer, (if escape p G a then (1 : ℚ) else 0) ≤ Fintype.card Answer * η)
    (hopen : ∀ p r G, eligible p r G →
      ∑ b : Answer, (if opens p r G b then (1 : ℚ) else 0) ≤ Fintype.card Answer * ρ) :
    (∑ G : Pt → Answer, ∑ p : Init, ∑ r : Opening,
      if (firstOfTwo tree G (initial p) (opening p r) = .left ∧ eligible p r G ∧
        escape p G (G (initial p))) ∧ opens p r G (G (opening p r)) then (1 : ℚ) else 0) ≤
      (η * ρ) * ∑ G : Pt → Answer, ∑ p : Init,
        if initial p ∈ queried tree G then (1 : ℚ) else 0 := by
  have hl := CanonicalOpening125.parentFirst_relation_sum_le tree initial opening
    eligible escape opens ρ hρ hne hunique
    (fun p r G G' h _ => heligible p r G G' h)
    (fun p r G G' h _ => hescapeOpen p r G G' h)
    (fun p r G G' h _ => hopens p r G G' h) (fun p r G _ => hopen p r G)
  have hi := CanonicalOpening125.observed_local_sum_le tree initial escape η hescapeInit hinit
  refine hl.trans ((mul_le_mul_of_nonneg_left hi hρ).trans_eq ?_)
  ring

end ParentFirstCount

end LfzkV1.CanonicalSecondary125
