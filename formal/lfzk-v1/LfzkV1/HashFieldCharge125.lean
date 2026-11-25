import LfzkV1.HashFieldPath125
import LfzkV1.RbrZkSplit
import LfzkV1.NizkZk

/-! Per-candidate field charges before the two terminal Ligero slots. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashFieldCharge125

open Finset LfzkV1.RbrZkLongfellow LfzkV1.RbrZkSplit LfzkV1.RbrLayerStepS
open LfzkV1.HashFieldPath125
open LfzkV1.ResidualReplay125 LfzkV1.CompiledZk LfzkV1.Arith LfzkV1.ZkArithProfile
open LfzkV1.NizkGrinding (slot_roleAt)
open scoped Classical

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc} {asg : Lift → LigeroAssignment ninp M F}
variable {Sat : Lift → Prop}

local notation "Role" => Rounds.Role nl w
local notation "State" => ZkState M ninp logw logc F X

def wrong (lift : Lift) (state : State) : Prop :=
  ZkWrong V H asg Sat (fun _ _ => False) (some lift) state

/-- The actual field transition. Its previous-coin argument is unused by
these roles. -/
noncomputable def fieldStep (msgs : ℕ → Msg) (role : Role) (coin : C) (state : State) : State :=
  match role with
  | .layerPair ly => if ly.val = 0 then zkInit V coin state
      else zkCombine nl w V (V.closeOf (msgs role.slot)) coin state
  | .sumcheck _ _ => zkRound V (V.roundOf (msgs role.slot)) coin state
  | .inputBind => zkInputBind nl w V (V.closeOf (msgs role.slot)) coin state
  | .ligeroChallenge | .ligeroQuery => state

def escapes (msgs : ℕ → Msg) (role : Role) (lift : Lift) (state : State) (coin : C) : Prop :=
  wrong (V := V) (H := H) (asg := asg) (Sat := Sat) lift state ∧
    ¬ wrong (V := V) (H := H) (asg := asg) (Sat := Sat) lift
      (fieldStep (V := V) msgs role coin state)

omit [Fintype C] [Fintype F] in
theorem initial_escapes_iff (msgs : ℕ → Msg) (ly : Fin nl) (hly : ly.val = 0)
    (lift : Lift) (coin : C) :
    escapes (V := V) (H := H) (asg := asg) (Sat := Sat) msgs (Rounds.Role.layerPair (w := w) ly)
      lift .start coin ↔
      ¬ Sat lift ∧ (∀ j, ¬ H.Pend lift j []) ∧
        H.sum lift 0 (V.st0 (V.decodeInit coin).1) (V.decodeInit coin).2.1
          (V.decodeInit coin).2.2 [] = 0 := by
  simp [escapes, wrong, fieldStep, hly, zkInit, ZkWrong, RowsBad]
  intro _
  constructor
  · rintro ⟨hz, hpend, hfuture⟩
    refine ⟨?_, hz.symm⟩
    intro j hp
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact hpend hp
    · exact hfuture j hpos hp
  · rintro ⟨hpend, hz⟩
    exact ⟨hz.symm, hpend 0, fun j _ => hpend j⟩

omit [Fintype C] [Fintype F] [DecidableEq F] in
theorem fieldStep_eq_atS (msgs : ℕ → Msg) (role : Role)
    (hrole : role.slot < Rounds.Role.layerBase w nl + 1)
    (pref : Fin role.slot → C) (coin : C) (s : State) :
    stepAtS (zkSteps nl w V msgs (fun _ _ _ _ => Finset.empty)) role role.slot pref coin s =
      fieldStep (V := V) msgs role coin s := by
  cases role <;> simp_all [Rounds.Role.slot, stepAtS, zkSteps, fieldStep]

variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]

def oneLiftBudget (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (role : Role) : ℕ :=
  match role with
  | .layerPair ly => if ly.val = 0 then FD.kinit * FD.binit else FD.kpair * (2 * Fintype.card F)
  | .sumcheck _ _ => FD.k * 2
  | .inputBind => FD.k
  | .ligeroChallenge | .ligeroQuery => 0

def oneLiftNumerator (logv : ℕ) (role : Role) : ℕ :=
  match role with
  | .layerPair ly => if ly.val = 0 then logv + 2 else 2
  | .sumcheck _ _ => 2
  | .inputBind => 1
  | .ligeroChallenge | .ligeroQuery => 0

omit [SumcheckV1Interp F] in
/-- The actual decoder widths cancel from a one-lift charge. The initial
slot uses the joint multilinear bound and later slots cost at most two. -/
theorem oneLiftBudget_scaled [Fintype X] {logv : ℕ}
    {code : ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc}
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M ninp logw logc nl w code H asg Sat)
    (hexact : FD.ExactAt) (role : Role) :
    oneLiftBudget FD role * Fintype.card F ≤ oneLiftNumerator logv role * Fintype.card C := by
  let q := Fintype.card F
  cases role with
  | layerPair ly =>
    by_cases h0 : ly.val = 0
    · simp only [oneLiftBudget, oneLiftNumerator, if_pos h0]
      calc
        FD.kinit * FD.binit * q ≤ FD.kinit * ((logv + 2) * q ^ (logv + 1)) * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hexact.1)
        _ = (logv + 2) * (FD.kinit * q ^ (logv + 2)) := by rw [pow_succ]; ring
        _ ≤ _ := Nat.mul_le_mul_left _ hexact.2.1
    · simp only [oneLiftBudget, oneLiftNumerator, if_neg h0]
      calc
        FD.kpair * (2 * q) * q = 2 * (FD.kpair * (q * q)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hexact.2.2.1
  | sumcheck ly j =>
    simp only [oneLiftBudget, oneLiftNumerator]
    calc
      FD.k * 2 * q = 2 * (FD.k * q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hexact.2.2.2.1
  | inputBind => simpa [oneLiftBudget, oneLiftNumerator] using hexact.2.2.2.1
  | ligeroChallenge | ligeroQuery => simp [oneLiftBudget, oneLiftNumerator]

theorem escapes_card_le (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (msgs : ℕ → Msg) (role : Role) (lift : Lift) (state : State) :
    (univ.filter (escapes (V := V) (H := H) (asg := asg) (Sat := Sat) msgs role lift state)).card ≤
      oneLiftBudget FD role := by
  by_cases hw : wrong (V := V) (H := H) (asg := asg) (Sat := Sat) lift state
  · change ZkWrong V H asg Sat (fun _ _ => False) (some lift) state at hw
    cases role with
    | layerPair ly =>
      by_cases hi : ly.val = 0
      · simpa [escapes, wrong, fieldStep, hi, oneLiftBudget, hw, wt] using
          zkInit_budget V H asg Sat (fun _ _ => False) FD.kinit FD.binit FD.hbalInit FD.hinit
            (some lift) state hw
      · simpa [escapes, wrong, fieldStep, hi, oneLiftBudget, hw, wt] using
          zkCombine_budget (Sat := Sat) (LigDoomed := fun _ _ => False) FD.B
            (V.closeOf (msgs (Rounds.Role.layerPair (w := w) ly).slot)) FD.kpair FD.hbalPair
            (some lift) state hw
    | sumcheck ly j =>
      simpa [escapes, wrong, fieldStep, oneLiftBudget, hw, wt] using
        zkRound_budget (Sat := Sat) (LigDoomed := fun _ _ => False) FD.B
          (V.roundOf (msgs (Rounds.Role.sumcheck ly j).slot)) FD.k FD.hbalF (some lift) state hw
    | inputBind =>
      simpa [escapes, wrong, fieldStep, oneLiftBudget, hw, wt] using
        zkInputBind_budget (Sat := Sat) (LigDoomed := fun _ _ => False) FD.B
          (V.closeOf (msgs (Rounds.Role.inputBind : Role).slot)) FD.k FD.hbalF (some lift) state hw
    | ligeroChallenge | ligeroQuery => simp [escapes, fieldStep, oneLiftBudget]
  · simp [escapes, hw]

/-- Primary lifts and lifts with pending assertions use the ordinary doom
transition. For the other lifts the same local budget pays for repairs. -/
def laterBad (boundary : ZkBoundary V H asg nl w) (primary : Option Lift)
    (msgs : ℕ → Msg) (role : Role) (lift : Lift) (state : State) (coin : C) : Prop :=
  if primary = some lift ∨ ∃ j, H.Pend lift j [] then
    escapes (V := V) (H := H) (asg := asg) (Sat := Sat) msgs role lift state coin
  else RepairAt boundary lift msgs role state coin

theorem laterBad_card_le (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (primary : Option Lift) (msgs : ℕ → Msg) (role : Role) (lift : Lift) (state : State)
    (hshape : ∀ zs, role = .inputBind → state = .running zs →
      zs.bound.length = w zs.layer ∧ zs.layer + 1 = nl) :
    (univ.filter (laterBad (Sat := Sat) FD.B primary msgs role lift state)).card ≤
      oneLiftBudget FD role := by
  by_cases h : primary = some lift ∨ ∃ j, H.Pend lift j []
  · simpa only [laterBad, if_pos h] using escapes_card_le FD msgs role lift state
  · rw [show laterBad (Sat := Sat) FD.B primary msgs role lift state =
        RepairAt FD.B lift msgs role state by funext coin; simp [laterBad, h]]
    have hr := repairAt_card_le FD.B lift msgs role state FD.kpair FD.k
      (by
        intro y
        convert FD.hbalPair y using 2
        ext _
        simp)
      (by
        intro y
        convert FD.hbalF y using 2
        ext _
        simp) hshape
    refine hr.trans ?_
    cases role <;> simp only [oneLiftBudget]
    · split_ifs <;> omega
    all_goals exact le_rfl

/-- Later transcript queries pay for up to the two fixed lifts of their
commitment, with one local rule for each lift. -/
theorem laterBad_union_card_le [Fintype Lift]
    (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (primary : Option Lift) (msgs : ℕ → Msg) (role : Role) (state : State)
    (hshape : ∀ zs, role = .inputBind → state = .running zs →
      zs.bound.length = w zs.layer ∧ zs.layer + 1 = nl) :
    (univ.filter fun coin : C => ∃ lift : Lift,
      laterBad (Sat := Sat) FD.B primary msgs role lift state coin).card ≤
      Fintype.card Lift * oneLiftBudget FD role := by
  let localSet := fun lift : Lift => univ.filter (laterBad (Sat := Sat) FD.B primary msgs role lift state)
  have he : (univ.filter fun coin : C => ∃ lift : Lift,
      laterBad (Sat := Sat) FD.B primary msgs role lift state coin) = univ.biUnion localSet := by
    ext coin
    simp [localSet]
  rw [he, ← card_univ (α := Lift)]
  apply card_biUnion_le_card_mul
  intro lift _
  exact laterBad_card_le FD primary msgs role lift state hshape

section Scheduled

variable {c : QuadCircuit F} {logv : ℕ}
variable (code : ZkCode C F X Q Msg (Fin logv → F) M c.ninp logw 0)
variable {honest : ZkHonest F Lift logw 0} {assignment : Lift → LigeroAssignment c.ninp M F}
variable {pub : Fin c.ninp → F}

omit [Fintype C] [DecidableEq X] [Fintype Q] [DecidableEq Q] in
/-- A selected lift satisfying the compiled system either pays for a later
field transition, escapes at initialization as the primary lift, or has a
canonical continuation that escaped at initialization as a secondary lift. -/
theorem selected_field_path (hpos : 0 < c.nl) (hcode : CodeAgreesP c pub logw code)
    (hst0 : ∀ G, (code.st0 G).g0 = padG logw G ∧ (code.st0 G).g1 = padG logw G)
    (boundary : ZkBoundary code honest assignment c.nl w) (primary : Option Lift)
    (messages : ℕ → Msg) (tape : Fin (Rounds.Role.length c.nl w) → C)
    (lift : Lift) (hfalse : ¬ Sat lift) (sys : LigeroSystem c.ninp M F)
    (hBuilt : zkBuilt (w := w) code messages tape = some sys)
    (hsat : sys.Sat (assignment lift).1 (assignment lift).2) :
    let init : Rounds.Role c.nl w := .layerPair ⟨0, hpos⟩
    let initEscape := escapes (V := code) (H := honest) (asg := assignment) (Sat := Sat)
      messages init lift .start (tape init.index)
    (∃ role : Rounds.Role c.nl w, 0 < role.slot ∧ role.slot < Rounds.Role.layerBase w c.nl + 1 ∧
      laterBad (Sat := Sat) boundary primary messages role lift
        (tapeState (w := w) code messages tape role.slot) (tape role.index)) ∨
      (primary = some lift ∧ initEscape) ∨
      (primary ≠ some lift ∧ initEscape ∧ CanonicalRun code messages boundary lift tape) := by
  dsimp only
  let ending := Rounds.Role.layerBase w c.nl + 1
  let init : Rounds.Role c.nl w := .layerPair ⟨0, hpos⟩
  have hlen : ending ≤ Rounds.Role.length c.nl w := by simp [ending, Rounds.Role.length]
  have hinit : init.slot = 0 := by simp [init, Rounds.Role.slot, Rounds.Role.layerBase]
  have hone : Rounds.Role.layerBase w 1 = 1 + w 0 := by simp [Rounds.Role.layerBase]
  let doomed := fun i => wrong (V := code) (H := honest) (asg := assignment) (Sat := Sat)
    lift (tapeState (w := w) code messages tape i)
  have hstart : tapeState (w := w) code messages tape 0 = .start := by
    rw [tapeState_eq code messages tape (Nat.zero_le _)]
    rfl
  have hfinal : tapeState (w := w) code messages tape ending = .built sys := by
    rw [tapeState_eq code messages tape hlen]
    exact builtOf_eq_some.mp hBuilt
  by_cases hlater : ∃ role : Rounds.Role c.nl w, 0 < role.slot ∧ role.slot < ending ∧
      laterBad (Sat := Sat) boundary primary messages role lift
        (tapeState (w := w) code messages tape role.slot) (tape role.index)
  · exact Or.inl hlater
  right
  by_cases hord : primary = some lift ∨ ∃ j, honest.Pend lift j []
  · have hds : doomed 0 := by simpa only [doomed, hstart, wrong, ZkWrong] using hfalse
    have hde : ¬ doomed ending := by simp [doomed, hfinal, wrong, ZkWrong, hsat]
    have hf : ∃ i < ending, doomed i ∧ ¬ doomed (i + 1) := by
      by_contra! hn
      have hall (i : ℕ) (hi : i ≤ ending) : doomed i := by
        induction i with
        | zero => exact hds
        | succ i ih => exact hn i (by omega) (ih (by omega))
      exact hde (hall ending le_rfl)
    obtain ⟨j, hj, hd, he⟩ := hf
    let role : Rounds.Role c.nl w := LfzkV1.NizkGrinding.roleAt j
    have hs : role.slot = j := slot_roleAt (hj.trans_le hlen)
    have hs_lt : role.slot < ending := by rw [hs]; exact hj
    have hstep := (tapeState_step code messages tape role).trans
      (fieldStep_eq_atS (V := code) messages role hs_lt _ _ _)
    have hesc : escapes (V := code) (H := honest) (asg := assignment) (Sat := Sat)
        messages role lift (tapeState (w := w) code messages tape role.slot) (tape role.index) := by
      refine ⟨?_, ?_⟩
      · rw [hs]; exact hd
      · rw [← hstep, hs]; exact he
    have hj0 : j = 0 := by
      by_contra hn
      apply hlater
      exact ⟨role, by omega, hs_lt, by simpa only [laterBad, if_pos hord] using hesc⟩
    have heq : role = init := by
      apply Rounds.Role.index_bijective.1
      apply Fin.ext
      show role.slot = init.slot
      rw [hs, hj0, hinit]
    have hi := hesc
    rw [heq, hinit, hstart] at hi
    have hh := (initial_escapes_iff messages ⟨0, hpos⟩ rfl lift (tape init.index)).mp hi
    exact Or.inl ⟨hord.resolve_right (fun ⟨j, hj⟩ => hh.2.1 j hj), hi⟩
  · have hnPrimary : primary ≠ some lift := fun h => hord (Or.inl h)
    have hnPend (j : ℕ) : ¬ honest.Pend lift j [] := fun h => hord (Or.inr ⟨j, h⟩)
    have hn (role : Rounds.Role c.nl w) :
        ¬ RepairAt boundary lift messages role
          (tapeState (w := w) code messages tape role.slot) (tape role.index) := by
      intro h
      have hfield : 0 < role.slot ∧ role.slot < ending := by
        cases role with
        | layerPair ly =>
          by_cases hz : ly.val = 0
          · exfalso
            revert h
            cases tapeState (w := w) code messages tape (Rounds.Role.layerPair (w := w) ly).slot <;>
              simp [RepairAt, hz]
          · have hmono := Rounds.Role.layerBase_mono (w := w) (show 1 ≤ ly.val by omega)
            have htop := Rounds.Role.layerBase_mono (w := w) ly.isLt.le
            rw [hone] at hmono
            simp only [Rounds.Role.slot, ending]
            omega
        | sumcheck ly j =>
          have hlt := j.isLt
          have htop := Rounds.Role.layerBase_mono (w := w) (Nat.succ_le_of_lt ly.isLt)
          rw [Rounds.Role.layerBase_succ] at htop
          simp only [Rounds.Role.slot, ending]
          omega
        | inputBind =>
          have hmono := Rounds.Role.layerBase_mono (w := w) hpos
          rw [hone] at hmono
          simp only [Rounds.Role.slot, ending]
          omega
        | ligeroChallenge | ligeroQuery =>
          exfalso
          revert h
          cases tapeState (w := w) code messages tape _ <;> simp [RepairAt]
      exact hlater ⟨role, hfield.1, hfield.2, by simpa only [laterBad, if_neg hord] using h⟩
    have hpath := canonical_of_built_no_repair code messages hpos hcode hst0 boundary lift tape hBuilt hsat hn
    exact Or.inr ⟨hnPrimary, (initial_escapes_iff messages ⟨0, hpos⟩ rfl lift _).mpr
      ⟨hfalse, hnPend, hpath.initial_zero code messages hpos⟩, hpath⟩

end Scheduled

end LfzkV1.HashFieldCharge125
