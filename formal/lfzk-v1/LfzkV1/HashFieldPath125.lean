import LfzkV1.CanonicalField125
import LfzkV1.ResidualReplay125Run

/-! A successful v1 field run has canonical transmitted fields unless a later slot repairs it. -/

open BigOperators SumcheckV1
open LfzkV1.Arith LfzkV1.CompiledZk LfzkV1.RbrZkLongfellow
open LfzkV1.ZkArithProfile LfzkV1.ZkArithInit LfzkV1.ResidualReplay125

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashFieldPath125

open CanonicalField125

variable {C F X Q Msg Gpt Lift : Type} [Field F] [Fintype F]
variable {M ninp L logc nl : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg Gpt M ninp L logc}
variable {H : ZkHonest F Lift L logc} {asg : Lift → LigeroAssignment ninp M F}
variable (B : ZkBoundary V H asg nl w) (ℓ : Lift)

/-- The de-padded running claim equals the selected lift's honest partial sum. -/
def Right (H : ZkHonest F Lift L logc) (ℓ : Lift) (pad : Pad M F)
    (zs : ZkRunning M L logc F) : Prop :=
  evaluates_to zs.e pad = H.sum ℓ zs.layer zs.st zs.beta zs.alpha zs.bound

variable [SumcheckV1Interp F]

/-- The two serialized evaluations at a sumcheck round. The third is reconstructed from the claim. -/
def RoundCanonical (H : ZkHonest F Lift L logc) (ℓ : Lift) (pad : Pad M F)
    (zs : ZkRunning M L logc F) (rm : ZkRoundMsg M F) : Prop :=
  (rm.tr0, rm.tr2) = roundFields (H.poly ℓ zs.layer zs.st zs.beta zs.alpha zs.bound)
    pad rm.pp0 rm.pp2

omit [SumcheckV1Interp F] in
/-- The de-padded endpoint pair agrees with the lift at the next layer's two points. -/
def CloseCanonical (zs : ZkRunning M L logc F) (cm : ZkCloseMsg M F) : Prop :=
  B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0 =
    (cm.wc0 + (asg ℓ).2 cm.dwL, cm.wc1 + (asg ℓ).2 cm.dwR)

omit [SumcheckV1Interp F] in
/-- With scheduled pad indices, a canonical close determines both serialized field values. -/
theorem closeFields_eq_of_canonical (zs : ZkRunning M L logc F) (cm : ZkCloseMsg M F)
    (hc : CloseCanonical B ℓ zs cm) :
    let W := B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0
    (cm.wc0, cm.wc1) = (W.1 - (asg ℓ).2 cm.dwL, W.2 - (asg ℓ).2 cm.dwR) := by
  dsimp only [CloseCanonical] at hc
  simp only [hc, add_sub_cancel_right]

/-- Repair events are resolved from the slot's running state, its fixed message, and its
answer. The hypotheses defining each bad input are precisely those of the local repair counts. -/
def RepairAt (ms : ℕ → Msg) (rl : Rounds.Role nl w) (state : ZkState M ninp L logc F X)
    (coin : C) : Prop :=
  match state, rl with
  | .running zs, .sumcheck _ _ =>
    let rm := V.roundOf (ms rl.slot)
    let r := V.decodeF coin
    (¬ Right H ℓ (asg ℓ).2 zs ∨ ¬ RoundCanonical H ℓ (asg ℓ).2 zs rm) ∧
      evaluates_to (builder_next zs.e (roundData rm r)) (asg ℓ).2 =
        H.sum ℓ zs.layer zs.st zs.beta zs.alpha (zs.bound ++ [r])
  | .running zs, .layerPair ly =>
    let cm := V.closeOf (ms rl.slot)
    let rb := V.decodePair coin
    ly.val ≠ 0 ∧
      (∃ b, B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b ≠
        (cm.wc0 + (asg ℓ).2 cm.dwL, cm.wc1 + (asg ℓ).2 cm.dwR)) ∧
      evaluates_to (builder_first rb.2 cm.wc0 cm.wc1 cm.dwL cm.dwR) (asg ℓ).2 =
        H.sum ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) rb.1 rb.2 []
  | .running zs, .inputBind =>
    let cm := V.closeOf (ms rl.slot)
    ¬ CloseCanonical B ℓ zs cm ∧
      (inputSystem V zs cm (V.decodeF coin)).Sat (asg ℓ).1 (asg ℓ).2
  | _, _ => False

open Classical in
/-- The repair predicate has the available raw-answer count for its actual role. -/
theorem repairAt_card_le [Fintype C] (ms : ℕ → Msg) (rl : Rounds.Role nl w)
    (s : ZkState M ninp L logc F X) (kPair kScalar : ℕ)
    (hPair : ∀ y : F × F, (Finset.univ.filter fun a : C => V.decodePair a = y).card ≤ kPair)
    (hScalar : ∀ y : F, (Finset.univ.filter fun a : C => V.decodeF a = y).card ≤ kScalar)
    (hInput : ∀ zs, rl = .inputBind → s = .running zs →
      zs.bound.length = w zs.layer ∧ zs.layer + 1 = nl) :
    (Finset.univ.filter (RepairAt B ℓ ms rl s)).card ≤
      match rl with
      | .layerPair ly => if ly.val = 0 then 0 else kPair * (2 * Fintype.card F)
      | .sumcheck _ _ => kScalar * 2
      | .inputBind => kScalar
      | _ => 0 := by
  cases s with
  | running zs =>
    cases rl with
    | sumcheck ly j =>
      let rm := V.roundOf (ms (Rounds.Role.sumcheck ly j).slot)
      by_cases hb : ¬ Right H ℓ (asg ℓ).2 zs ∨ ¬ RoundCanonical H ℓ (asg ℓ).2 zs rm
      · refine (Finset.card_le_card ?_).trans
          (zkRound_repair_card_le V H (asg ℓ).2 ℓ zs rm kScalar hScalar hb)
        intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩
      · simp [RepairAt, rm, hb]
    | layerPair ly =>
      let cm := V.closeOf (ms (Rounds.Role.layerPair (w := w) ly).slot)
      by_cases hzero : ly.val = 0
      · simp [RepairAt, hzero]
      · simp only [if_neg hzero]
        by_cases hb : ∃ b : F, B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b ≠
            (cm.wc0 + (asg ℓ).2 cm.dwL, cm.wc1 + (asg ℓ).2 cm.dwR)
        · refine (Finset.card_le_card ?_).trans (zkCombine_repair_card_le B ℓ zs cm kPair hPair hb)
          intro a ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2.2⟩
        · simp [RepairAt, cm, hb]
    | inputBind =>
      let cm := V.closeOf (ms (Rounds.Role.inputBind (nl := nl) (w := w)).slot)
      by_cases hb : CloseCanonical B ℓ zs cm
      · simp [RepairAt, cm, hb]
      · obtain ⟨hlen, hlast⟩ := hInput zs rfl rfl
        have hc := zkInput_repair_card_le B ℓ zs cm hlen hlast kScalar hScalar hb
        rw [Nat.mul_one] at hc
        refine (Finset.card_le_card ?_).trans hc
        intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩
    | ligeroChallenge => simp [RepairAt]
    | ligeroQuery => simp [RepairAt]
  | _ => simp [RepairAt]

section Scheduled

variable {c : QuadCircuit F} {logv : ℕ}
variable (code : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0) (ms : ℕ → Msg)
variable {honest : ZkHonest F Lift L 0} {assignment : Lift → LigeroAssignment c.ninp M F}

local notation "Role" => Rounds.Role c.nl w
local notation "Tape" => Fin (Rounds.Role.length c.nl w) → C

/-- These are the fields the verifier consumes at each actual slot of the run. -/
structure CanonicalRun (boundary : ZkBoundary code honest assignment c.nl w) (lift : Lift)
    (tape : Tape) : Prop where
  initial : ∃ zs, tapeState (w := w) code ms tape (Rounds.Role.layerBase w 0 + 1) = .running zs ∧
    Right honest lift (assignment lift).2 zs
  round : ∀ (ly : Fin c.nl) (j : Fin (w ly.val)) zs,
    tapeState (w := w) code ms tape (Rounds.Role.sumcheck ly j).slot = .running zs →
    RoundCanonical honest lift (assignment lift).2 zs (code.roundOf (ms (Rounds.Role.sumcheck ly j).slot))
  close : ∀ (ly : Fin c.nl) zs,
    tapeState (w := w) code ms tape (Rounds.Role.layerBase w ly.val + 1 + w ly.val) = .running zs →
    CloseCanonical boundary lift zs (closeMsg (w := w) code ms ly)

/-- The right initial claim is exactly zero at the grouped initial draw. -/
theorem CanonicalRun.initial_zero {boundary : ZkBoundary code honest assignment c.nl w}
    {lift : Lift} {tape : Tape} (path : CanonicalRun code ms boundary lift tape) (hpos : 0 < c.nl) :
    let rl : Role := .layerPair ⟨0, hpos⟩
    let draw := code.decodeInit (tape rl.index)
    honest.sum lift 0 (code.st0 draw.1) draw.2.1 draw.2.2 [] = 0 := by
  let rl : Role := .layerPair ⟨0, hpos⟩
  obtain ⟨zs, hzs, hright⟩ := path.initial
  have hpost : tapeState (w := w) code ms tape (rl.slot + 1) = .running zs := hzs
  have hs := tapeState_step code ms tape rl
  rw [hpost] at hs
  change .running zs = zkInit code (tape rl.index)
    (tapeState (w := w) code ms tape (Rounds.Role.layerBase w 0)) at hs
  have hstart : tapeState (w := w) code ms tape (Rounds.Role.layerBase w 0) = .start := by
    have hbase : Rounds.Role.layerBase w 0 = 0 := by simp [Rounds.Role.layerBase]
    rw [hbase, tapeState_eq code ms tape (Nat.zero_le _)]
    rfl
  rw [hstart, zkInit] at hs
  rw [ZkState.running.inj hs] at hright
  exact hright.symm.trans (_root_.Expression.evaluates_to_zero _)

omit [Fintype F] in
private theorem right_after_round (lift : Lift) (tape : Tape)
    (ly : Fin c.nl) (j : Fin (w ly.val)) {zs next : ZkRunning M L 0 F}
    (hpre : tapeState (w := w) code ms tape (Rounds.Role.sumcheck ly j).slot = .running zs)
    (hpost : tapeState (w := w) code ms tape ((Rounds.Role.sumcheck ly j).slot + 1) = .running next)
    (hright : Right honest lift (assignment lift).2 next) :
    let rl := Rounds.Role.sumcheck ly j
    let r := code.decodeF (tape rl.index)
    evaluates_to (builder_next zs.e (roundData (code.roundOf (ms rl.slot)) r)) (assignment lift).2 =
      honest.sum lift zs.layer zs.st zs.beta zs.alpha (zs.bound ++ [r]) := by
  let rl : Role := .sumcheck ly j
  have hs := tapeState_step code ms tape rl
  rw [hpre, hpost] at hs
  change ZkState.running next =
    zkRound code (code.roundOf (ms rl.slot)) (tape rl.index) (.running zs) at hs
  change ZkState.running next = ZkState.running _ at hs
  rw [ZkState.running.inj hs] at hright
  exact hright

omit [Fintype F] in
private theorem right_after_pair (lift : Lift) (tape : Tape)
    (ly : Fin c.nl) {zs next : ZkRunning M L 0 F} (hne : ly.val ≠ 0)
    (hpre : tapeState (w := w) code ms tape (Rounds.Role.layerPair (w := w) ly).slot = .running zs)
    (hpost : tapeState (w := w) code ms tape ((Rounds.Role.layerPair (w := w) ly).slot + 1) = .running next)
    (hguard : zs.bound.length = w zs.layer ∧ zs.layer + 1 < c.nl)
    (hright : Right honest lift (assignment lift).2 next) :
    let rl := Rounds.Role.layerPair (w := w) ly
    let cm := code.closeOf (ms rl.slot)
    let rb := code.decodePair (tape rl.index)
    evaluates_to (builder_first rb.2 cm.wc0 cm.wc1 cm.dwL cm.dwR) (assignment lift).2 =
      honest.sum lift (zs.layer + 1) (code.stNext zs.bound cm.wc0 cm.wc1) rb.1 rb.2 [] := by
  let rl : Role := .layerPair ly
  have hs := tapeState_step code ms tape rl
  rw [hpre, hpost] at hs
  change .running next =
    (if ly.val = 0 then zkInit code (tape rl.index) (.running zs)
     else zkCombine c.nl w code (code.closeOf (ms rl.slot)) (tape rl.index) (.running zs)) at hs
  rw [if_neg hne, zkCombine, if_pos hguard] at hs
  rw [ZkState.running.inj hs] at hright
  exact hright

variable [DecidableEq F] {pub : Fin c.ninp → F}

omit [Fintype F] in
/-- Every scheduled input-binding state has the prescribed final round count. -/
theorem input_state_shape (hpos : 0 < c.nl)
    (hV : CodeAgreesP c pub L code)
    (hst0 : ∀ G, (code.st0 G).g0 = padG L G ∧ (code.st0 G).g1 = padG L G)
    (tape : Tape) {zs : ZkRunning M L 0 F}
    (hz : tapeState (w := w) code ms tape (Rounds.Role.layerBase w c.nl) = .running zs) :
    zs.bound.length = w zs.layer ∧ zs.layer + 1 = c.nl := by
  let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
  have hlast : last.val + 1 = c.nl := by simp [last, Nat.sub_add_cancel (show 1 ≤ c.nl by omega)]
  have hbase : Rounds.Role.layerBase w last.val + 1 + w last.val = Rounds.Role.layerBase w c.nl := calc
    _ = Rounds.Role.layerBase w (last.val + 1) := by rw [Rounds.Role.layerBase_succ]; omega
    _ = _ := congrArg (Rounds.Role.layerBase w) hlast
  let P := FieldTape.ofRaw code tape hpos
  let x : Empty → F := fun e => nomatch e
  have hrun := tapeState_after_rounds code ms P hV hst0 x tape
    (FieldTape.matches_ofRaw code tape hpos x) last (w last.val) le_rfl
  rw [hbase] at hrun
  rw [ZkState.running.inj (hz.symm.trans hrun)]
  refine ⟨?_, hlast⟩
  change (afterRounds code ms P x last (w last.val)).bound.length = w last.val
  simp [FieldTape.bound]

omit [SumcheckV1Interp F] in
/-- The honest endpoint pair in the profiled arithmetization uses only the hand points.
A canonical close therefore determines its own two serialized fields from the previous prefix
and the scheduled padding indices. -/
theorem closeFields_profiled (hV : CodeAgreesP c pub L code)
    (boundary : ZkBoundary code honest assignment c.nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : boundary.W = zkWP pub wOf)
    (lift : Lift) (zs : ZkRunning M L 0 F) (cm : ZkCloseMsg M F)
    (hc : CloseCanonical boundary lift zs cm) :
    let expected := boundary.W lift (zs.layer + 1) (code.stNext zs.bound 0 0) 0
    (cm.wc0, cm.wc1) =
      (expected.1 - (assignment lift).2 cm.dwL, expected.2 - (assignment lift).2 cm.dwR) := by
  have hclose := closeFields_eq_of_canonical boundary lift zs cm hc
  have he : boundary.W lift (zs.layer + 1) (code.stNext zs.bound cm.wc0 cm.wc1) 0 =
      boundary.W lift (zs.layer + 1) (code.stNext zs.bound 0 0) 0 := by
    simp only [hW, zkWP, (hV.hst _ _ _).1, (hV.hst _ _ _).2]
  dsimp only at hclose ⊢
  rwa [he] at hclose

omit [Fintype F] [SumcheckV1Interp F] in
/-- With no violated intermediate assertions, the honest intermediate pair is independent
of the next beta. -/
theorem profiled_pair_beta_eq (hde : c.DeadEnd) (wOf : Lift → Fin c.ninp → F) (lift : Lift)
    (ly : ℕ) (hly : ly < c.nl) (st : LayerState L 0 F) (b : F)
    (hassert : ∀ j, c.assertVec pub (wOf lift) ly j = 0) :
    zkWP pub wOf lift ly st b = zkWP pub wOf lift ly st 0 := by
  simp [zkWP, VP_decomp hde pub (wOf lift) hly, mle, hassert]

/-- Absence of a repair forces the whole successful path to use canonical ordinary fields.
The argument proceeds backward from the passing input row through actual pairs and rounds. -/
theorem canonical_of_built_no_repair (hpos : 0 < c.nl)
    (hV : CodeAgreesP c pub L code)
    (hst0 : ∀ G, (code.st0 G).g0 = padG L G ∧ (code.st0 G).g1 = padG L G)
    (boundary : ZkBoundary code honest assignment c.nl w) (lift : Lift)
    (tape : Tape) {sys : LigeroSystem c.ninp M F}
    (hBuilt : zkBuilt (w := w) code ms tape = some sys)
    (hSat : sys.Sat (assignment lift).1 (assignment lift).2)
    (hNo : ∀ rl : Role, ¬ RepairAt boundary lift ms rl
      (tapeState (w := w) code ms tape rl.slot) (tape rl.index)) :
    CanonicalRun code ms boundary lift tape := by
  let P := FieldTape.ofRaw code tape hpos
  let x : Empty → F := fun e => nomatch e
  let S := afterRounds code ms P x
  let pad := (assignment lift).2
  have hm := FieldTape.matches_ofRaw code tape hpos x
  have hS (ly : Fin c.nl) (j : ℕ) (hj : j ≤ w ly.val) :
      tapeState (w := w) code ms tape (Rounds.Role.layerBase w ly.val + 1 + j) = .running (S ly j) :=
    tapeState_after_rounds code ms P hV hst0 x tape hm ly j hj
  have hlayer (ly : Fin c.nl) (j : ℕ) : (S ly j).layer = ly.val := rfl
  have hbound (ly : Fin c.nl) : (S ly (w ly.val)).bound.length = w ly.val := by
    change (afterRounds code ms P x ly (w ly.val)).bound.length = w ly.val
    rw [afterRounds_full_bound]
    simp [FieldTape.bound]
  have hend (ly : Fin c.nl) (hc : CloseCanonical boundary lift (S ly (w ly.val))
      (closeMsg (w := w) code ms ly)) : Right honest lift pad (S ly (w ly.val)) := by
    apply claim_eq_of_canonical_close boundary lift _ _ ((hbound ly).trans (congrArg w (hlayer ly _).symm))
      (by rw [hlayer]; exact ly.isLt) _ hc
    exact layer_checks_of_running_zkBuilt code ms hV hst0 tape ly
      (hS ly _ le_rfl) hBuilt _ _ hSat
  have hround (ly : Fin c.nl) (j : Fin (w ly.val)) :
      Right honest lift pad (S ly (j.val + 1)) →
      Right honest lift pad (S ly j.val) ∧
      RoundCanonical honest lift pad (S ly j.val) (code.roundOf (ms (Rounds.Role.sumcheck ly j).slot)) := by
    intro hright
    let rl : Role := .sumcheck ly j
    have hp : tapeState (w := w) code ms tape rl.slot = .running (S ly j.val) :=
      hS ly _ j.isLt.le
    have hq : tapeState (w := w) code ms tape (rl.slot + 1) = .running (S ly (j.val + 1)) := by
      change tapeState (w := w) code ms tape (Rounds.Role.layerBase w ly.val + 1 + j.val + 1) = _
      rw [Nat.add_assoc]
      exact hS ly _ j.isLt
    have hh := right_after_round (honest := honest) (assignment := assignment) code ms lift tape ly j hp hq hright
    have hn := hNo rl
    rw [hp] at hn
    change ¬ ((¬ Right honest lift pad (S ly j.val) ∨
      ¬ RoundCanonical honest lift pad (S ly j.val) (code.roundOf (ms rl.slot))) ∧ _) at hn
    exact not_or.mp (fun hb => hn ⟨hb, hh⟩) |>.imp not_not.mp not_not.mp
  have hrounds (ly : Fin c.nl) (hterm : Right honest lift pad (S ly (w ly.val))) :
      Right honest lift pad (S ly 0) ∧
      ∀ j : Fin (w ly.val), RoundCanonical honest lift pad (S ly j.val)
        (code.roundOf (ms (Rounds.Role.sumcheck ly j).slot)) := by
    let canon := fun j => ∀ (hj : j < w ly.val),
      RoundCanonical honest lift pad (S ly j) (code.roundOf (ms (Rounds.Role.sumcheck ly ⟨j, hj⟩).slot))
    rcases canonical_or_repair (fun j => Right honest lift pad (S ly j)) canon (fun _ => False)
        (w ly.val) hterm (fun j hj hr => Or.inl ⟨(hround ly ⟨j, hj⟩ hr).1,
          fun _ => (hround ly ⟨j, hj⟩ hr).2⟩) with ⟨h0, hall⟩ | ⟨_, _, hfalse⟩
    · exact ⟨h0, fun j => hall j.val j.isLt j.isLt⟩
    · exact hfalse.elim
  have hclose : ∀ (d : ℕ) (ly : Fin c.nl), c.nl - (ly.val + 1) = d →
      CloseCanonical boundary lift (S ly (w ly.val)) (closeMsg (w := w) code ms ly) := by
    intro d
    induction d with
    | zero =>
      intro ly hd
      let rl : Role := .inputBind
      have hlast : ly.val + 1 = c.nl := by have := ly.isLt; omega
      have hbase : Rounds.Role.layerBase w ly.val + 1 + w ly.val = rl.slot := calc
        _ = Rounds.Role.layerBase w (ly.val + 1) := by rw [Rounds.Role.layerBase_succ]; omega
        _ = _ := congrArg (Rounds.Role.layerBase w) hlast
      have hp : tapeState (w := w) code ms tape rl.slot = .running (S ly (w ly.val)) := by
        rw [← hbase]
        exact hS ly _ le_rfl
      have hs := inputSystem_eq_of_running_zkBuilt code ms tape hp hBuilt
      have ht : (inputSystem code (S ly (w ly.val)) (code.closeOf (ms rl.slot))
          (code.decodeF (tape rl.index))).Sat (assignment lift).1 pad := hs ▸ hSat
      have hn := hNo rl
      rw [hp] at hn
      change ¬ ((¬ CloseCanonical boundary lift (S ly (w ly.val)) (code.closeOf (ms rl.slot))) ∧ _) at hn
      have htCanon : CloseCanonical boundary lift (S ly (w ly.val)) (code.closeOf (ms rl.slot)) :=
        not_not.mp fun hb => hn ⟨hb, ht⟩
      simpa [closeMsg, hlast] using htCanon
    | succ d ih =>
      intro ly hd
      let next : Fin c.nl := ⟨ly.val + 1, by omega⟩
      let rl : Role := .layerPair next
      have hnz : next.val ≠ 0 := by simp [next]
      have hnext : c.nl - (next.val + 1) = d := by dsimp [next]; omega
      have hright := (hrounds next (hend next (ih next hnext))).1
      have hbase : Rounds.Role.layerBase w ly.val + 1 + w ly.val = rl.slot := by
        change _ = Rounds.Role.layerBase w (ly.val + 1)
        rw [Rounds.Role.layerBase_succ]
        omega
      have hp : tapeState (w := w) code ms tape rl.slot = .running (S ly (w ly.val)) := by
        rw [← hbase]
        exact hS ly _ le_rfl
      have hq : tapeState (w := w) code ms tape (rl.slot + 1) = .running (S next 0) :=
        hS next 0 (Nat.zero_le _)
      have hg : (S ly (w ly.val)).bound.length = w (S ly (w ly.val)).layer ∧
          (S ly (w ly.val)).layer + 1 < c.nl := by
        change (S ly (w ly.val)).bound.length = w ly.val ∧ ly.val + 1 < c.nl
        exact ⟨hbound ly, next.isLt⟩
      have ht := right_after_pair (honest := honest) (assignment := assignment) code ms lift tape
        next hnz hp hq hg hright
      have hn := hNo rl
      rw [hp] at hn
      let cm := code.closeOf (ms rl.slot)
      have hc : CloseCanonical boundary lift (S ly (w ly.val)) cm := by
        by_contra hb
        exact hn ⟨hnz, ⟨0, hb⟩, ht⟩
      simpa [closeMsg, next, rl, cm, pairMsg, next.isLt] using hc
  have hc (ly : Fin c.nl) := hclose _ ly rfl
  have hr (ly : Fin c.nl) := hrounds ly (hend ly (hc ly))
  refine ⟨⟨S ⟨0, hpos⟩ 0, hS ⟨0, hpos⟩ 0 (Nat.zero_le _), (hr ⟨0, hpos⟩).1⟩, ?_, ?_⟩
  · intro ly j zs hz
    have h := hS ly j.val j.isLt.le
    rw [ZkState.running.inj (hz.symm.trans h)]
    exact (hr ly).2 j
  · intro ly zs hz
    rw [ZkState.running.inj (hz.symm.trans (hS ly _ le_rfl))]
    exact hc ly

end Scheduled

end LfzkV1.HashFieldPath125
