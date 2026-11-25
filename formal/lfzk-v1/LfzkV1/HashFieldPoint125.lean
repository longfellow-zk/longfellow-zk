import LfzkV1.HashFieldCharge125
import LfzkV1.CanonicalOpening125
import LfzkV1.CompiledZkDeployedHash

/-! The field charges at the actual legacy message-prefix inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashFieldPoint125

open Finset LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.ResidualReplay125
open LfzkV1.RbrZkLongfellow LfzkV1.RbrZkSplit LfzkV1.CompiledZk
open LfzkV1.NizkDeployedHash LfzkV1.CanonicalOpening125 LfzkV1.HashFieldCharge125
open LfzkV1.HashFieldPath125 (input_state_shape)
open scoped Classical

variable {C F X Q Msg Lift Ctx : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] [Inhabited Msg] {c : QuadCircuit F} {w : ℕ → ℕ}
variable {M L logv : ℕ} {V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0}
variable {H : ZkHonest F Lift L 0} {asg : Lift → LigeroAssignment c.ninp M F} {Sat : Lift → Prop}

local notation "Role" => Rounds.Role c.nl w
local notation "Point" => MPoint Ctx Msg c.nl w

noncomputable def pointState (V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0)
    (p : Point) (pref : Fin p.role.slot → C) : ZkState M c.ninp L 0 F X :=
  (zkRun (nl := c.nl) (w := w) V p.msgFn (fun _ _ _ _ => ∅)).state p.role.slot pref

/-- An initial query pays only for the primary lift. A later field query
can pay for either lift. The terminal Ligero points have their own charges. -/
def bad (B : ZkBoundary V H asg c.nl w) (primary : Option Lift)
    (p : Point) (pref : Fin p.role.slot → C) (coin : C) : Prop :=
  if p.role.slot = 0 then ∃ x, primary = some x ∧
    escapes (V := V) (H := H) (asg := asg) (Sat := Sat) p.msgFn p.role x (pointState V p pref) coin
  else if p.role.slot < Rounds.Role.layerBase w c.nl + 1 then ∃ x,
    laterBad (Sat := Sat) B primary p.msgFn p.role x (pointState V p pref) coin
  else False

omit [Fintype C] [Fintype F] in
private theorem pointState_input_shape [Nonempty C] {pub : Fin c.ninp → F}
    (hpos : 0 < c.nl) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (p : Point) (pref : Fin p.role.slot → C) {zs : ZkRunning M L 0 F}
    (hrole : p.role = .inputBind) (hs : pointState V p pref = .running zs) :
    zs.bound.length = w zs.layer ∧ zs.layer + 1 = c.nl := by
  let tape : Fin (Rounds.Role.length c.nl w) → C := fun i =>
    if h : i.val < p.role.slot then pref ⟨i.val, h⟩ else Classical.arbitrary C
  have hpre : Bcs.trunc tape p.role.slot p.role.slot_lt.le = pref := by
    funext i
    change (if h : i.val < p.role.slot then pref ⟨i.val, h⟩ else Classical.arbitrary C) = pref i
    rw [dif_pos i.isLt]
  have hrun := tapeState_eq V p.msgFn tape p.role.slot_lt.le
  rw [hpre] at hrun
  have he : tapeState (w := w) V p.msgFn tape p.role.slot = .running zs := hrun.trans hs
  have hi : p.role.slot = Rounds.Role.layerBase w c.nl := congrArg (fun rl : Role => rl.slot) hrole
  rw [hi] at he
  exact input_state_shape V p.msgFn hpos hV hst0 tape he

variable [Fintype Lift] [DecidableEq X] [Fintype X] [Fintype Q] [DecidableEq Q]

omit [Inhabited Msg] [Fintype Lift] in
theorem initial_escape_scaled_card_le
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 c.nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (msgs : ℕ → Msg)
    (ly : Fin c.nl) (hly : ly.val = 0) (lift : Lift) :
    (univ.filter (escapes (V := V) (H := H) (asg := asg) (Sat := Sat)
      msgs (.layerPair (w := w) ly) lift .start)).card * Fintype.card F ≤
      7 * Fintype.card C := by
  let role : Role := .layerPair ly
  have hcap : oneLiftNumerator logv role ≤ 7 := by simp only [role, oneLiftNumerator, if_pos hly]; omega
  exact (Nat.mul_le_mul_right _ (escapes_card_le FD msgs role lift .start)).trans
    ((oneLiftBudget_scaled FD hexact role).trans (Nat.mul_le_mul_right _ hcap))

/-- A uniform transcript-query cap for the actual hash field point. -/
theorem bad_scaled_card_le [Nonempty C] {pub : Fin c.ninp → F}
    (hpos : 0 < c.nl) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 c.nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (hlist : Fintype.card Lift ≤ 2)
    (primary : Option Lift) (p : Point) (pref : Fin p.role.slot → C) :
    (univ.filter (bad (Sat := Sat) FD.B primary p pref)).card * Fintype.card F ≤
      (if p.role.slot = 0 then 7 else 4) * Fintype.card C := by
  have hbudget := oneLiftBudget_scaled FD hexact p.role
  by_cases hinitial : p.role.slot = 0
  · have hcap : oneLiftNumerator logv p.role ≤ 7 := by
      cases p.role <;> simp [oneLiftNumerator, apply_ite (fun n : ℕ => n ≤ 7), hlogv]
    rw [if_pos hinitial]
    cases primary with
    | none => simp [bad, hinitial]
    | some x =>
      have h := escapes_card_le FD p.msgFn p.role x (pointState V p pref)
      have hc := (Nat.mul_le_mul_right (Fintype.card F) h).trans hbudget
      exact (by simpa [bad, hinitial] using hc.trans (Nat.mul_le_mul_right _ hcap))
  · rw [if_neg hinitial]
    by_cases hfield : p.role.slot < Rounds.Role.layerBase w c.nl + 1
    · have hcap : oneLiftNumerator logv p.role ≤ 2 := by
        cases hp : p.role with
        | layerPair ly =>
          have hn : ly.val ≠ 0 := by
            intro hz
            apply hinitial
            simp [hp, Rounds.Role.slot, hz, Rounds.Role.layerBase]
          simp [oneLiftNumerator, hn]
        | _ => simp [oneLiftNumerator]
      have h := laterBad_union_card_le FD primary p.msgFn p.role (pointState V p pref)
        (fun zs hr hs => pointState_input_shape hpos hV hst0 p pref hr hs)
      calc
        _ ≤ (Fintype.card Lift * oneLiftBudget FD p.role) * Fintype.card F := by
          simpa only [bad, if_neg hinitial, if_pos hfield] using Nat.mul_le_mul_right _ h
        _ = Fintype.card Lift * (oneLiftBudget FD p.role * Fintype.card F) := by rw [Nat.mul_assoc]
        _ ≤ 2 * (2 * Fintype.card C) := Nat.mul_le_mul hlist
          (hbudget.trans (Nat.mul_le_mul_right _ hcap))
        _ = _ := by ring
    · simp [bad, hinitial, hfield]

omit [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F] [Inhabited Msg]
  [Fintype Lift] [DecidableEq X] [Fintype X] [Fintype Q] [DecidableEq Q] in
private theorem sum_indicator_le (event : C → Prop) (rate : ℕ)
    (h : (univ.filter event).card * 2 ^ 128 ≤ rate * Fintype.card C) :
    ∑ a : C, (if event a then (1 : ℚ) else 0) ≤ Fintype.card C * (rate / 2 ^ 128) := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact_mod_cast (by rwa [Nat.mul_comm rate] at h :
    (univ.filter event).card * 2 ^ 128 ≤ Fintype.card C * rate)

omit [Inhabited Msg] [Fintype Lift] in
theorem initial_escape_sum_le
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 c.nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (hq : Fintype.card F = 2 ^ 128)
    (msgs : ℕ → Msg) (ly : Fin c.nl) (hly : ly.val = 0) (lift : Lift) :
    (∑ a : C, if escapes (V := V) (H := H) (asg := asg) (Sat := Sat)
      msgs (.layerPair (w := w) ly) lift .start a then (1 : ℚ) else 0) ≤
      Fintype.card C * (7 / 2 ^ 128) := by
  apply sum_indicator_le _ 7
  simpa only [hq] using initial_escape_scaled_card_le FD hexact hlogv msgs ly hly lift

theorem bad_sum_le [Nonempty C] {pub : Fin c.ninp → F}
    (hpos : 0 < c.nl) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (FD : ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 c.nl w V H asg Sat)
    (hexact : FD.ExactAt) (hlogv : logv ≤ 5) (hlist : Fintype.card Lift ≤ 2)
    (hq : Fintype.card F = 2 ^ 128) (primary : Option Lift) (p : Point) (pref : Fin p.role.slot → C) :
    (∑ a : C, if bad (Sat := Sat) FD.B primary p pref a then (1 : ℚ) else 0) ≤
      Fintype.card C * ((if p.role.slot = 0 then 7 else 4) / 2 ^ 128) := by
  have hb := bad_scaled_card_le hpos hV hst0 FD hexact hlogv hlist primary p pref
  by_cases h : p.role.slot = 0
  · simp only [h, if_true, hq] at hb ⊢
    exact sum_indicator_le _ 7 hb
  · simp only [h, if_false, hq] at hb ⊢
    exact sum_indicator_le _ 4 hb

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Lift] [DecidableEq X] [Fintype X]
  [Fintype Q] [DecidableEq Q] in
private theorem state_of_run (ctx : Ctx) (oracle : Point → C) (msgs : ℕ → Msg)
    (role : Role) :
    let p := msgPoint ctx (fun f i => f i) msgs role.slot
    pointState V p (mpoints.chal oracle p) =
      tapeState (w := w) V msgs (fun i => oracle (msgPoint ctx (fun f j => f j) msgs i.val)) role.slot := by
  dsimp only
  rw [tapeState_eq V msgs _ role.slot_lt.le]
  exact state_at_msgPoint (fun ms => zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => ∅))
    (LfzkV1.CompiledZkDeployedHash.zkRun_msgLocal V (fun _ _ _ _ => ∅)) ctx oracle msgs role.index

omit [Fintype C] [DecidableEq F] [Inhabited Msg] [Fintype Lift] [DecidableEq X]
  [Fintype X] [Fintype Q] [DecidableEq Q] in
private theorem laterBad_congr (B : ZkBoundary V H asg c.nl w) (primary : Option Lift)
    (a b : ℕ → Msg) (role : Role) (h : a role.slot = b role.slot)
    (lift : Lift) (s : ZkState M c.ninp L 0 F X) (coin : C) :
    laterBad (Sat := Sat) B primary a role lift s coin =
      laterBad (Sat := Sat) B primary b role lift s coin := by
  cases role <;> cases s <;> simp only [laterBad, escapes, fieldStep, HashFieldPath125.RepairAt, h]

omit [Fintype C] [DecidableEq F] [Fintype Lift] [DecidableEq X] [Fintype X] [Fintype Q] [DecidableEq Q] in
theorem bad_of_later_run (B : ZkBoundary V H asg c.nl w) (primary : Option Lift)
    (ctx : Ctx) (oracle : Point → C) (msgs : ℕ → Msg) (role : Role) (lift : Lift)
    (hpos : 0 < role.slot) (hfield : role.slot < Rounds.Role.layerBase w c.nl + 1)
    (h : laterBad (Sat := Sat) B primary msgs role lift
      (tapeState (w := w) V msgs (fun i => oracle (msgPoint ctx (fun f j => f j) msgs i.val)) role.slot)
      (oracle (msgPoint ctx (fun f j => f j) msgs role.slot))) :
    let p := msgPoint ctx (fun f i => f i) msgs role.slot
    bad (Sat := Sat) B primary p (mpoints.chal oracle p) (oracle p) := by
  dsimp only
  let p : Point := msgPoint ctx (fun f i => f i) msgs role.slot
  have hslot : p.role.slot = role.slot := slot_msgPoint ctx (fun f i => f i) msgs role.slot_lt
  have hrole : p.role = role := Rounds.Role.index_bijective.1 (Fin.ext hslot)
  have hmsg : p.msgFn role.slot = msgs role.slot := by
    exact msgFn_msgPoint ctx (fun f i => f i) msgs role.slot_lt le_rfl
  have hsfield : p.role.slot < Rounds.Role.layerBase w c.nl + 1 := by rw [hslot]; exact hfield
  change bad (Sat := Sat) B primary p (mpoints.chal oracle p) (oracle p)
  change laterBad (Sat := Sat) B primary msgs role lift _ (oracle p) at h
  unfold bad
  rw [if_neg (by omega : p.role.slot ≠ 0), if_pos hsfield]
  refine ⟨lift, ?_⟩
  rw [state_of_run ctx oracle msgs role, hrole, laterBad_congr B primary _ _ _ hmsg]
  exact h

omit [Fintype C] [Fintype Lift] [DecidableEq X] [Fintype X] [Fintype Q] [DecidableEq Q] in
theorem bad_of_primary_run (B : ZkBoundary V H asg c.nl w) (primary : Option Lift)
    (ctx : Ctx) (oracle : Point → C) (msgs : ℕ → Msg) (ly : Fin c.nl) (hly : ly.val = 0)
    (lift : Lift) (hprimary : primary = some lift)
    (h : escapes (V := V) (H := H) (asg := asg) (Sat := Sat) msgs (.layerPair (w := w) ly)
      lift .start (oracle (msgPoint ctx (fun f i => f i) msgs 0))) :
    let p : Point := msgPoint ctx (fun f i => f i) msgs 0
    bad (Sat := Sat) B primary p (mpoints.chal oracle p) (oracle p) := by
  dsimp only
  let r : Role := .layerPair ly
  let p : Point := msgPoint ctx (fun f i => f i) msgs 0
  have hz : r.slot = 0 := by simp [r, Rounds.Role.slot, Rounds.Role.layerBase, hly]
  have hp : p.role.slot = 0 := slot_msgPoint ctx (fun f i => f i) msgs (hz ▸ r.slot_lt)
  have hr : p.role = r := Rounds.Role.index_bijective.1 (Fin.ext (hp.trans hz.symm))
  have hstate : pointState V p (mpoints.chal oracle p) = .start := by
    have hs := state_of_run (V := V) ctx oracle msgs r
    rwa [show tapeState (w := w) V msgs _ r.slot = .start by
      rw [hz, tapeState_eq V msgs _ (Nat.zero_le _)]
      rfl, hz] at hs
  unfold bad
  rw [if_pos hp, hstate, hr]
  exact ⟨lift, hprimary, (initial_escapes_iff p.msgFn ly hly lift (oracle p)).mpr
    ((initial_escapes_iff msgs ly hly lift (oracle p)).mp h)⟩

end LfzkV1.HashFieldPoint125
