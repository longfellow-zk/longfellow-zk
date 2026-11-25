import LfzkV1.ResidualReplay125Profile
import LfzkV1.CompiledZk

/-! For fixed proof messages, the scheduled v1 field run evaluates one symbolic system. -/

open BigOperators MvPolynomial SumcheckV1
open LfzkV1.Arith LfzkV1.RbrZkLongfellow LfzkV1.ZkArithProfile LfzkV1.ZkArithInit
open LfzkV1.CompiledZk LfzkV1.CompiledLongfellow LfzkV1.RbrLayerStepS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ResidualReplay125

variable {σ : Type*} {F : Type} [Field F]

/-- Polynomial values of the ordinary field challenges, in the verifier's role schedule. -/
structure FieldTape (σ F : Type*) [Field F] (nl : ℕ) (w : ℕ → ℕ) (logv : ℕ) where
  G : Fin logv → Poly σ F
  beta : Fin nl → Poly σ F
  alpha : Fin nl → Poly σ F
  round : (ly : Fin nl) → Fin (w ly.val) → Poly σ F
  inputAlpha : Poly σ F

structure FieldTape.Bounded {nl : ℕ} {w : ℕ → ℕ} {logv : ℕ}
    (P : FieldTape σ F nl w logv) : Prop where
  G : ∀ i, (P.G i).totalDegree ≤ 1
  beta : ∀ ly, (P.beta ly).totalDegree ≤ 1
  alpha : ∀ ly, (P.alpha ly).totalDegree ≤ 1
  round : ∀ ly j, (P.round ly j).totalDegree ≤ 1
  inputAlpha : P.inputAlpha.totalDegree ≤ 1

/-- Evaluation agrees with the actual configured decoder for every field role. -/
structure FieldTape.Matches {C₀ X₀ Q Msg : Type} {M ninp L nl logv : ℕ} {w : ℕ → ℕ}
    (P : FieldTape σ F nl w logv) (V : ZkCode C₀ F X₀ Q Msg (Fin logv → F) M ninp L 0)
    (x : σ → F) (tape : Fin (Rounds.Role.length nl w) → C₀) : Prop where
  init : ∀ ly : Fin nl, ly.val = 0 →
    V.decodeInit (tape (Rounds.Role.layerPair (w := w) ly).index) =
      (fun j => eval x (P.G j), eval x (P.beta ly), eval x (P.alpha ly))
  pair : ∀ ly : Fin nl, ly.val ≠ 0 →
    V.decodePair (tape (Rounds.Role.layerPair (w := w) ly).index) =
      (eval x (P.beta ly), eval x (P.alpha ly))
  round : ∀ (ly : Fin nl) (j : Fin (w ly.val)),
    V.decodeF (tape (Rounds.Role.sumcheck ly j).index) = eval x (P.round ly j)
  input : V.decodeF (tape (Rounds.Role.inputBind (nl := nl) (w := w)).index) = eval x P.inputAlpha

section Schedule

variable {C₀ X₀ Q Msg : Type} {c : QuadCircuit F} {M L logv : ℕ} {w : ℕ → ℕ}
variable (V : ZkCode C₀ F X₀ Q Msg (Fin logv → F) M c.ninp L 0) (ms : ℕ → Msg)

local notation "Role" => Rounds.Role c.nl w
local notation "RawTape" => Fin (Rounds.Role.length c.nl w) → C₀

def pairMsg (ly : Fin c.nl) : ZkCloseMsg M F :=
  V.closeOf (ms (Rounds.Role.layerPair (w := w) ly).slot)

/-- The upcoming pair consumes this layer's close, or the input binding consumes it at
the last layer. -/
def closeMsg (ly : Fin c.nl) : ZkCloseMsg M F :=
  if h : ly.val + 1 < c.nl then pairMsg (w := w) V ms ⟨ly.val + 1, h⟩
  else V.closeOf (ms (Rounds.Role.inputBind (nl := c.nl) (w := w)).slot)

variable (P : FieldTape σ F c.nl w logv)

def FieldTape.rounds (ly : Fin c.nl) : List (Round σ F M) :=
  List.ofFn fun j => replayRound (V.roundOf (ms (Rounds.Role.sumcheck ly j).slot)) (P.round ly j)

@[simp] theorem FieldTape.rounds_length (ly : Fin c.nl) :
    (P.rounds V ms ly).length = w ly.val := by simp [FieldTape.rounds]

theorem FieldTape.rounds_degree (hP : P.Bounded) (ly : Fin c.nl) :
    ∀ r ∈ P.rounds V ms ly, r.challenge.totalDegree ≤ 1 := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact hP.round ly j

noncomputable def FieldTape.bound (ly : Fin c.nl) : List (Poly σ F) :=
  List.ofFn (P.round ly)

theorem FieldTape.round_challenges (ly : Fin c.nl) :
    (P.rounds V ms ly).map Round.challenge = P.bound ly := by
  simp [FieldTape.rounds, FieldTape.bound, List.map_ofFn, Function.comp_def, replayRound]

theorem FieldTape.bound_degree (hP : P.Bounded) (ly : Fin c.nl) :
    ∀ r ∈ P.bound ly, r.totalDegree ≤ 1 := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact hP.round ly j

/-- Before the first layer the incoming claim is zero. A later layer folds the preceding
close message, at exactly the alpha decoded for this layer. -/
noncomputable def FieldTape.start (ly : Fin c.nl) : Expression σ F M :=
  if ly.val = 0 then Expression.zero
  else
    let cm := pairMsg (w := w) V ms ly
    Expression.first (P.alpha ly) cm.wc0 cm.wc1 cm.dwL cm.dwR

theorem FieldTape.start_degree (hP : P.Bounded) (ly : Fin c.nl) :
    (P.start V ms ly).Bounded 1 := by
  unfold FieldTape.start
  split_ifs
  · exact Expression.zero_bounded 1
  · exact Expression.first_bounded (hP.alpha ly) _ _ _ _

/-- The initial point is repeated. Subsequent points are the preceding layer's two hands. -/
noncomputable def FieldTape.gatePoint (ly : Fin c.nl) (side : Fin 2) (j : Fin L) : Poly σ F :=
  if h : ly.val = 0 then initial P.G j
  else hand (P.bound ⟨ly.val - 1, by have := ly.isLt; omega⟩) side j

variable [DecidableEq F]

noncomputable def FieldTape.layer (ly : Fin c.nl) : Layer σ F M :=
  profiledLayer c ly.val (P.gatePoint ly 0 : Fin L → Poly σ F) (P.gatePoint ly 1)
    (P.beta ly) (P.alpha ly) (P.start V ms ly) (P.rounds V ms ly) (closeMsg (w := w) V ms ly)

noncomputable def FieldTape.inputRow (pub : Fin c.ninp → F) (hpos : 0 < c.nl) :
    Row σ F c.ninp M :=
  let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
  profiledInput c pub (P.bound last) P.inputAlpha (closeMsg (w := w) V ms last) L

variable [SumcheckV1Interp F]

/-- Compile every close row, then the single input row, with the fixed quadratic pad triples. -/
noncomputable def FieldTape.system (pub : Fin c.ninp → F) (hpos : 0 < c.nl) :
    System σ F c.ninp M :=
  ⟨(List.ofFn fun ly => (P.layer V ms ly).row) ++ [P.inputRow V ms pub hpos],
    List.ofFn fun ly =>
      let cm := closeMsg (w := w) V ms ly
      (cm.dwL, cm.dwR, cm.dwLR)⟩

theorem FieldTape.system_bounded81 (pub : Fin c.ninp → F) (hpos : 0 < c.nl)
    {R : CertifiedV1.Row} (hR : V7HashProfile R) (hnl : c.nl = R.params.nl)
    (hw : w = R.params.rounds) (hlogv : logv ≤ 5) (hP : P.Bounded) :
    (P.system V ms pub hpos).Bounded 81 := by
  have width_le (ly : Fin c.nl) : R.params.logw ly.val ≤ 20 :=
    v7_hash_width hR _ (hnl ▸ ly.isLt)
  have round_count (ly : Fin c.nl) : w ly.val = 2 * R.params.logw ly.val := by
    rw [hw, CostV1.Params.rounds]
  have gate_le (ly : Fin c.nl) : ow logv R.params.logw ly.val ≤ 20 := by
    cases h : ly.val with
    | zero => exact hlogv.trans (by decide)
    | succ i => exact v7_hash_gate_width hR (i + 1) (Nat.le_of_lt (hnl ▸ h ▸ ly.isLt))
  have gate_degree (ly : Fin c.nl) (s : Fin 2) (j : Fin L) :
      (P.gatePoint ly s j).totalDegree ≤ if j.val < ow logv R.params.logw ly.val then 1 else 0 := by
    by_cases h : ly.val = 0
    · rw [FieldTape.gatePoint, dif_pos h]
      simpa only [h, ow] using degree_initial hP.G j
    · rw [FieldTape.gatePoint, dif_neg h]
      let prev : Fin c.nl := ⟨ly.val - 1, by have := ly.isLt; omega⟩
      have hw' : ow logv R.params.logw ly.val = R.params.logw prev.val := by
        cases hly : ly.val with
        | zero => exact (h hly).elim
        | succ j => simp [ow, prev, hly]
      rw [hw']
      exact degree_hand (by simpa [FieldTape.bound] using round_count prev)
        (P.bound_degree hP prev) s j
  intro row hrow
  change row ∈ (List.ofFn fun ly => (P.layer V ms ly).row) ++ [P.inputRow V ms pub hpos] at hrow
  rcases List.mem_append.mp hrow with hl | hi
  · obtain ⟨ly, rfl⟩ := List.mem_ofFn.mp hl
    exact profiledLayer_bounded81 c ly.val _ (gate_le ly) (width_le ly) (hP.beta ly) (hP.alpha ly)
      (gate_degree ly 0) (gate_degree ly 1) (P.start_degree V ms hP ly)
      ((P.rounds_length V ms ly).trans (round_count ly)) (P.rounds_degree V ms hP ly)
  · have he := List.mem_singleton.mp hi
    subst row
    let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
    have h := degree_profiledInput c pub (closeMsg (w := w) V ms last) L
      (R.params.logw last.val) (by simpa [FieldTape.bound] using round_count last)
      (P.bound_degree hP last) hP.inputAlpha
    have hd : 1 + R.params.logw last.val ≤ 81 := by have := width_le last; omega
    exact ⟨fun i => (h.1 i).trans hd, fun j => (h.2.1 j).trans hd, h.2.2.trans hd⟩

end Schedule

section Run

variable {C₀ X₀ Q Msg : Type} {c : QuadCircuit F} {M L logv : ℕ} {w : ℕ → ℕ}
variable (V : ZkCode C₀ F X₀ Q Msg (Fin logv → F) M c.ninp L 0) (ms : ℕ → Msg)
variable (P : FieldTape σ F c.nl w logv)

local notation "Role" => Rounds.Role c.nl w
local notation "RawTape" => Fin (Rounds.Role.length c.nl w) → C₀

/-- A single actual tape can be used as a replay with no variable coordinates. -/
noncomputable def FieldTape.ofRaw (tape : RawTape) (hpos : 0 < c.nl) :
    FieldTape Empty F c.nl w logv :=
  let coin := fun ly => tape (Rounds.Role.layerPair (w := w) ly).index
  let pair := fun ly : Fin c.nl =>
    if ly.val = 0 then (V.decodeInit (coin ly)).2 else V.decodePair (coin ly)
  { G := fun j => C ((V.decodeInit (coin ⟨0, hpos⟩)).1 j)
    beta := fun ly => C (pair ly).1
    alpha := fun ly => C (pair ly).2
    round := fun ly j => C (V.decodeF (tape (Rounds.Role.sumcheck ly j).index))
    inputAlpha := C (V.decodeF (tape (Rounds.Role.inputBind (nl := c.nl) (w := w)).index)) }

theorem FieldTape.matches_ofRaw (tape : RawTape) (hpos : 0 < c.nl) (x : Empty → F) :
    (FieldTape.ofRaw V tape hpos).Matches V x tape := by
  constructor
  · intro ly h
    have he : ly = ⟨0, hpos⟩ := Fin.ext h
    subst ly
    simp [FieldTape.ofRaw]
  · intro ly h
    simp [FieldTape.ofRaw, h]
  · intro ly j
    simp [FieldTape.ofRaw]
  · simp [FieldTape.ofRaw]

variable [DecidableEq F] [SumcheckV1Interp F]
variable {pub : Fin c.ninp → F}
variable (hV : CodeAgreesP c pub L V)
variable (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
variable (x : σ → F)

private noncomputable def layerState (ly : Fin c.nl) : LayerState L 0 F :=
  if h : ly.val = 0 then V.st0 (fun j => eval x (P.G j))
  else
    let prev : Fin c.nl := ⟨ly.val - 1, by have := ly.isLt; omega⟩
    let cm := pairMsg (w := w) V ms ly
    V.stNext ((P.bound prev).map (eval x)) cm.wc0 cm.wc1

private noncomputable def rowsBefore (i : ℕ) : List (LayerRowData M F) :=
  (List.ofFn fun j => (P.layer V ms j).data x).take i

private theorem rowsBefore_succ (ly : Fin c.nl) :
    rowsBefore V ms P x (ly.val + 1) =
      rowsBefore V ms P x ly.val ++ [(P.layer V ms ly).data x] := by
  unfold rowsBefore
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using ly.isLt),
    List.getElem_ofFn]

/-- The state at the start of a layer, advanced by its first `j` rounds. -/
noncomputable def afterRounds (ly : Fin c.nl) (j : ℕ) : ZkRunning M L 0 F :=
  let rs := (P.rounds V ms ly).take j
  { layer := ly.val
    beta := eval x (P.beta ly)
    st := layerState V ms P x ly
    alpha := eval x (P.alpha ly)
    bound := rs.map fun r => eval x r.challenge
    e := builder_run ((P.start V ms ly).eval x) (rs.map (Round.eval x))
    rows := rowsBefore V ms P x ly.val }

@[simp] theorem afterRounds_full_bound (ly : Fin c.nl) :
    (afterRounds V ms P x ly (w ly.val)).bound = (P.bound ly).map (eval x) := by
  unfold afterRounds
  rw [List.take_of_length_le (by simp), ← P.round_challenges V ms ly, List.map_map]
  rfl

include hV hst0 in
private theorem afterRounds_close (ly : Fin c.nl) :
    (P.layer V ms ly).data x =
      closeRow V (afterRounds V ms P x ly (w ly.val)) (closeMsg (w := w) V ms ly) := by
  have hleft :
      (Vector.ofFn fun j : Fin L => eval x (P.gatePoint ly 0 j)) = (layerState V ms P x ly).g0 := by
    by_cases h : ly.val = 0
    · simp only [FieldTape.gatePoint, layerState, dif_pos h, eval_initial, (hst0 _).1]
    · simp only [FieldTape.gatePoint, layerState, dif_neg h, eval_hand_left, (hV.hst _ _ _).1]
  have hright :
      (Vector.ofFn fun j : Fin L => eval x (P.gatePoint ly 1 j)) = (layerState V ms P x ly).g1 := by
    by_cases h : ly.val = 0
    · simp only [FieldTape.gatePoint, layerState, dif_pos h, eval_initial, (hst0 _).2]
    · simp only [FieldTape.gatePoint, layerState, dif_neg h, eval_hand_right, (hV.hst _ _ _).2]
  unfold FieldTape.layer
  apply eval_profiledLayer hV x (afterRounds V ms P x ly (w ly.val)) ly.isLt
    _ _ _ _ _ _ _ hleft hright rfl rfl
  · rw [afterRounds_full_bound, ← P.round_challenges V ms ly, List.map_map]
    rfl
  · simp only [afterRounds, ← P.rounds_length V ms ly, List.take_length]

omit [DecidableEq F] in
private theorem builder_run_snoc (e : _root_.Expression M F) (rs : List (RoundData M F))
    (r : RoundData M F) : builder_run e (rs ++ [r]) = builder_next (builder_run e rs) r := by
  induction rs generalizing e with
  | nil => rfl
  | cons q qs ih => exact ih _

/-- The scheduled verifier state just before slot `m`, for a full verifier tape. -/
noncomputable def tapeState (tape : RawTape) (m : ℕ) :
    ZkState M c.ninp L 0 F X₀ :=
  if hle : m ≤ Rounds.Role.length c.nl w then
    (zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => Finset.empty)).state m (Bcs.trunc tape m hle)
  else .failed

omit [DecidableEq F] in
theorem tapeState_eq (tape : RawTape) {m : ℕ} (hm : m ≤ Rounds.Role.length c.nl w) :
    tapeState (w := w) V ms tape m =
      (zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => Finset.empty)).state m
        (Bcs.trunc tape m hm) :=
  dif_pos hm

omit [DecidableEq F] in
theorem tapeState_step (tape : RawTape) (rl : Role) :
    tapeState (w := w) V ms tape (rl.slot + 1) =
      stepAtS (zkSteps c.nl w V ms (fun _ _ _ _ => Finset.empty)) rl rl.slot
        (Bcs.trunc tape rl.slot rl.slot_lt.le) (tape rl.index)
        (tapeState (w := w) V ms tape rl.slot) := by
  unfold tapeState
  rw [dif_pos (Nat.succ_le_of_lt rl.slot_lt), dif_pos rl.slot_lt.le]
  let ch := zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => Finset.empty)
  calc
    _ = ch.step rl.index (Bcs.trunc tape rl.slot rl.slot_lt.le) (tape rl.index)
        (ch.state rl.slot (Bcs.trunc tape rl.slot rl.slot_lt.le)) :=
      state_trunc_succ ch tape rl.index
    _ = _ := chainS_step_index (zkSteps c.nl w V ms (fun _ _ _ _ => Finset.empty))
      (fun (_ : PUnit) _ => False) .start rl _ _ _

private theorem tapeState_rounds (tape : RawTape) (hm : P.Matches V x tape) (ly : Fin c.nl)
    (hstart : tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1) =
          .running (afterRounds V ms P x ly 0))
    (j : ℕ) (hj : j ≤ w ly.val) :
    tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1 + j) =
      .running (afterRounds V ms P x ly j) := by
  induction j with
  | zero => exact hstart
  | succ j ih =>
    let k : Fin (w ly.val) := ⟨j, by omega⟩
    have hs := tapeState_step V ms tape (Rounds.Role.sumcheck ly k)
    change tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1 + j + 1) = _ at hs
    rw [← Nat.add_assoc (Rounds.Role.layerBase w ly.val + 1) j 1, hs]
    have hp := ih (by omega)
    have hh : (P.rounds V ms ly).take (j + 1) =
        (P.rounds V ms ly).take j ++ [replayRound
          (V.roundOf (ms (Rounds.Role.sumcheck ly k).slot)) (P.round ly k)] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp [FieldTape.rounds, k]
    simp [stepAtS, zkSteps, Rounds.Role.slot, hp, zkRound, hm.round ly k,
      afterRounds, hh, builder_run_snoc, replayRound, Round.eval, roundData, k]

include hV hst0 in
private theorem tapeState_pair (tape : RawTape) (hm : P.Matches V x tape) (i : ℕ) (hi : i < c.nl) :
    tapeState (w := w) V ms tape (Rounds.Role.layerBase w i + 1) =
      .running (afterRounds V ms P x ⟨i, hi⟩ 0) := by
  induction i with
  | zero =>
    let ly : Fin c.nl := ⟨0, hi⟩
    have hs := tapeState_step V ms tape (Rounds.Role.layerPair (w := w) ly)
    change tapeState (w := w) V ms tape (Rounds.Role.layerBase w 0 + 1) = _ at hs
    rw [hs]
    change zkInit V (tape (Rounds.Role.layerPair (w := w) ly).index)
      (tapeState (w := w) V ms tape 0) =
      .running (afterRounds V ms P x ly 0)
    simp [tapeState, Bcs.ClaimChain.state, zkRun, layerStepChainS, zkInit, hm.init ly rfl,
      afterRounds, layerState, FieldTape.start, ly, rowsBefore, builder_run]
  | succ i ih =>
    let prev : Fin c.nl := ⟨i, by omega⟩
    let ly : Fin c.nl := ⟨i + 1, hi⟩
    have hbase : Rounds.Role.layerBase w prev.val + 1 + w prev.val =
        Rounds.Role.layerBase w ly.val := by
      rw [show ly.val = prev.val + 1 by rfl, Rounds.Role.layerBase_succ]
      omega
    have hfull := tapeState_rounds V ms P x tape hm prev (ih (by omega)) _ le_rfl
    rw [hbase] at hfull
    have hs := tapeState_step V ms tape (Rounds.Role.layerPair (w := w) ly)
    change tapeState (w := w) V ms tape (Rounds.Role.layerBase w (i + 1) + 1) = _ at hs
    rw [hs]
    have hnz : ly.val ≠ 0 := by simp [ly]
    simp only [stepAtS, zkSteps, if_neg hnz]
    rw [show (Rounds.Role.layerPair (w := w) ly).slot = Rounds.Role.layerBase w ly.val by rfl, hfull]
    have hclose : closeMsg (w := w) V ms prev = pairMsg (w := w) V ms ly := by
      simp [closeMsg, prev, ly, hi]
    have hrows := rowsBefore_succ V ms P x prev
    have heq := afterRounds_close V ms P hV hst0 x prev
    rw [hclose] at heq
    have hlen : (afterRounds V ms P x prev (w prev.val)).bound.length = w prev.val := by
      simp [FieldTape.bound]
    change zkCombine c.nl w V (pairMsg (w := w) V ms ly)
      (tape (Rounds.Role.layerPair (w := w) ly).index)
      (.running (afterRounds V ms P x prev (w prev.val))) = _
    rw [zkCombine, if_pos ⟨hlen, hi⟩, ← heq, afterRounds_full_bound]
    have hrows' : rowsBefore V ms P x (i + 1) =
        rowsBefore V ms P x prev.val ++ [(P.layer V ms prev).data x] :=
      hrows
    have hsucc : i + 1 ≠ 0 := Nat.succ_ne_zero i
    simp only [hm.pair ly hnz, afterRounds,
      List.take_zero, List.map_nil, layerState, FieldTape.start, dif_neg hsucc, if_neg hsucc,
      Expression.eval_first, builder_run, hrows']
    rfl

include hV hst0 in
/-- Every ordinary layer slot is running, with its previous rows and the expected round prefix. -/
theorem tapeState_after_rounds (tape : RawTape) (hm : P.Matches V x tape)
    (ly : Fin c.nl) (j : ℕ) (hj : j ≤ w ly.val) :
    tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1 + j) =
      .running (afterRounds V ms P x ly j) :=
  tapeState_rounds V ms P x tape hm ly
    (tapeState_pair V ms P hV hst0 x tape hm ly.val ly.isLt) j hj

omit P x in
include hV hst0 in
theorem tapeState_running (tape : RawTape) (ly : Fin c.nl) (j : ℕ) (hj : j ≤ w ly.val) :
    ∃ zs, tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1 + j) = .running zs := by
  have hpos : 0 < c.nl := by have := ly.isLt; omega
  let x : Empty → F := fun e => nomatch e
  exact ⟨_, tapeState_after_rounds V ms (FieldTape.ofRaw V tape hpos) hV hst0 x tape
    (FieldTape.matches_ofRaw V tape hpos x) ly j hj⟩

include hV hst0 in
private theorem rowsBefore_end (last : Fin c.nl) (hlast : last.val + 1 = c.nl) :
    rowsBefore V ms P x c.nl =
      (afterRounds V ms P x last (w last.val)).rows ++
        [closeRow V (afterRounds V ms P x last (w last.val)) (closeMsg (w := w) V ms last)] := by
  have h := rowsBefore_succ V ms P x last
  rw [hlast, afterRounds_close V ms P hV hst0 x last] at h
  exact h

include hV hst0 in
private theorem eval_system_inputSystem (hpos : 0 < c.nl)
    (last : Fin c.nl) (hlast : last.val + 1 = c.nl) :
    (P.system V ms pub hpos).eval x =
      inputSystem V (afterRounds V ms P x last (w last.val))
        (closeMsg (w := w) V ms last) (eval x P.inputAlpha) := by
  have hlast' : (⟨c.nl - 1, by omega⟩ : Fin c.nl) = last := by
    apply Fin.ext
    change c.nl - 1 = last.val
    omega
  have hin := eval_profiledInput hV x (P.bound last) P.inputAlpha (closeMsg (w := w) V ms last)
  unfold inputSystem
  rw [← rowsBefore_end V ms P hV hst0 x last hlast, afterRounds_full_bound]
  simp only [FieldTape.system, System.eval, FieldTape.inputRow, hlast', hin, buildSystemMulti,
    rowsBefore, List.map_append, List.map_ofFn, List.map_cons, List.map_nil, Function.comp_def,
    Layer.eval_row, FieldTape.layer, profiledLayer, Layer.data,
    List.take_of_length_le (List.length_ofFn.le)]

include hV hst0 in
/-- All completions with the same fixed messages build the evaluation of one system.
The fitting check depends only on the number of scheduled rows and triples. -/
theorem FieldTape.zkBuilt_eq_if (tape : RawTape) (hm : P.Matches V x tape) (hpos : 0 < c.nl) :
    zkBuilt (w := w) V ms tape = if c.nl + 1 ≤ V.nlin ∧ c.nl ≤ V.nt then
      some ((P.system V ms pub hpos).eval x) else none := by
  let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
  have hlast : last.val + 1 = c.nl := by simp [last, Nat.sub_add_cancel (show 1 ≤ c.nl by omega)]
  have hbase : Rounds.Role.layerBase w last.val + 1 + w last.val = Rounds.Role.layerBase w c.nl := by
    calc
      _ = Rounds.Role.layerBase w (last.val + 1) := by rw [Rounds.Role.layerBase_succ]; omega
      _ = _ := congrArg (Rounds.Role.layerBase w) hlast
  have hfull := tapeState_rounds V ms P x tape hm last
    (tapeState_pair V ms P hV hst0 x tape hm last.val last.isLt) _ le_rfl
  rw [hbase] at hfull
  have hclose : closeMsg (w := w) V ms last =
      V.closeOf (ms ((Rounds.Role.inputBind : Role).slot)) := by
    simp [closeMsg, hlast]
  have heval := eval_system_inputSystem V ms P hV hst0 x hpos last hlast
  have hfits : Fits V ((P.system V ms pub hpos).eval x) ↔ c.nl + 1 ≤ V.nlin ∧ c.nl ≤ V.nt := by
    simp [Fits, System.eval, FieldTape.system]
  change builtOf ((zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => Finset.empty)).state
    (Rounds.Role.layerBase w c.nl + 1) (Bcs.trunc tape _ fieldLen_le)) = _
  have hs := tapeState_step V ms tape (Rounds.Role.inputBind : Role)
  have hcut : (Rounds.Role.inputBind : Role).slot + 1 ≤ Rounds.Role.length c.nl w := fieldLen_le
  rw [tapeState, dif_pos hcut] at hs
  change (zkRun (nl := c.nl) (w := w) V ms (fun _ _ _ _ => Finset.empty)).state
    (Rounds.Role.layerBase w c.nl + 1) (Bcs.trunc tape _ fieldLen_le) = _ at hs
  rw [hs]
  change builtOf (zkInputBind c.nl w V (V.closeOf (ms ((Rounds.Role.inputBind : Role).slot)))
    (tape (Rounds.Role.inputBind : Role).index)
    (tapeState (w := w) V ms tape (Rounds.Role.layerBase w c.nl))) = _
  rw [hfull, ← hclose, zkInputBind, hm.input, ← heval]
  have hlen : (afterRounds V ms P x last (w last.val)).bound.length = w last.val := by
    simp [FieldTape.bound]
  have hg :
      ((afterRounds V ms P x last (w last.val)).bound.length =
        w (afterRounds V ms P x last (w last.val)).layer ∧
        (afterRounds V ms P x last (w last.val)).layer + 1 = c.nl ∧
        Fits V ((P.system V ms pub hpos).eval x)) ↔ c.nl + 1 ≤ V.nlin ∧ c.nl ≤ V.nt := by
    change (_ = w last.val ∧ last.val + 1 = c.nl ∧ _) ↔ _
    simp only [hlen, hlast, true_and, hfits]
  by_cases h : c.nl + 1 ≤ V.nlin ∧ c.nl ≤ V.nt
  · simp only [if_pos (hg.mpr h), if_pos h, builtOf]
  · simp only [if_neg (mt hg.mp h), if_neg h, builtOf]

include hV hst0 in
theorem FieldTape.zkBuilt_eq (tape : RawTape) (hm : P.Matches V x tape) (hpos : 0 < c.nl)
    (hlin : c.nl + 1 ≤ V.nlin) (hquad : c.nl ≤ V.nt) :
    zkBuilt (w := w) V ms tape = some ((P.system V ms pub hpos).eval x) := by
  simpa only [if_pos (And.intro hlin hquad)] using
    FieldTape.zkBuilt_eq_if V ms P hV hst0 x tape hm hpos

include hV hst0 in
/-- On a successful field build, a satisfying Ligero assignment satisfies the original
linear and quadratic close checks at every layer of the scheduled verifier. -/
theorem FieldTape.layer_checks_of_zkBuilt (tape : RawTape) (hm : P.Matches V x tape)
    (ly : Fin c.nl) {sys : LigeroSystem c.ninp M F}
    (hBuilt : zkBuilt (w := w) V ms tape = some sys)
    (wcol : Fin c.ninp → F) (pad : Pad M F) (hSat : sys.Sat wcol pad) :
    let row := closeRow V (afterRounds V ms P x ly (w ly.val)) (closeMsg (w := w) V ms ly)
    ligero_layer_checks row.e pad row.eqq row.wc0 row.wc1 row.var_dwL row.var_dwR row.var_dwLR := by
  have hpos : 0 < c.nl := by have := ly.isLt; omega
  let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
  have hlast : last.val + 1 = c.nl := by simp [last, Nat.sub_add_cancel (show 1 ≤ c.nl by omega)]
  rw [P.zkBuilt_eq_if V ms hV hst0 x tape hm hpos] at hBuilt
  split_ifs at hBuilt
  · have hsat : (inputSystem V (afterRounds V ms P x last (w last.val))
        (closeMsg (w := w) V ms last) (eval x P.inputAlpha)).Sat wcol pad := by
      rw [← eval_system_inputSystem V ms P hV hst0 x hpos last hlast, Option.some.inj hBuilt]
      exact hSat
    rw [inputSystem, buildSystemMulti_Sat] at hsat
    apply hsat.1
    rw [← rowsBefore_end V ms P hV hst0 x last hlast, rowsBefore,
      List.take_of_length_le List.length_ofFn.le, ← afterRounds_close V ms P hV hst0 x ly]
    exact List.mem_ofFn.mpr ⟨ly, rfl⟩

omit P x in
include hV hst0 in
theorem layer_checks_of_running_zkBuilt (tape : RawTape) (ly : Fin c.nl) {zs : ZkRunning M L 0 F}
    (hz : tapeState (w := w) V ms tape (Rounds.Role.layerBase w ly.val + 1 + w ly.val) = .running zs)
    {sys : LigeroSystem c.ninp M F} (hBuilt : zkBuilt (w := w) V ms tape = some sys)
    (wcol : Fin c.ninp → F) (pad : Pad M F) (hSat : sys.Sat wcol pad) :
    let row := closeRow V zs (closeMsg (w := w) V ms ly)
    ligero_layer_checks row.e pad row.eqq row.wc0 row.wc1 row.var_dwL row.var_dwR row.var_dwLR := by
  have hpos : 0 < c.nl := by have := ly.isLt; omega
  let x : Empty → F := fun e => nomatch e
  let P := FieldTape.ofRaw V tape hpos
  have hm := FieldTape.matches_ofRaw V tape hpos x
  have hrun := tapeState_after_rounds V ms P hV hst0 x tape hm ly (w ly.val) le_rfl
  rw [ZkState.running.inj (hz.symm.trans hrun)]
  exact P.layer_checks_of_zkBuilt V ms hV hst0 x tape hm ly hBuilt wcol pad hSat

omit [DecidableEq F] in
/-- A successful build took its constraint system from the actual input binding. -/
theorem inputSystem_eq_of_running_zkBuilt (tape : RawTape) {zs : ZkRunning M L 0 F}
    (hz : tapeState (w := w) V ms tape (Rounds.Role.layerBase w c.nl) = .running zs)
    {sys : LigeroSystem c.ninp M F} (hBuilt : zkBuilt (w := w) V ms tape = some sys) :
    let rl := (Rounds.Role.inputBind : Role)
    let cm := V.closeOf (ms rl.slot)
    let a := V.decodeF (tape rl.index)
    sys = inputSystem V zs cm a := by
  let rl : Role := .inputBind
  have hcut : rl.slot + 1 ≤ Rounds.Role.length c.nl w := fieldLen_le
  have hstate : tapeState (w := w) V ms tape (rl.slot + 1) = .built sys := by
    apply builtOf_eq_some.mp
    rw [tapeState_eq V ms tape hcut]
    exact hBuilt
  have hstep := tapeState_step V ms tape rl
  rw [hstate] at hstep
  have hz' : tapeState (w := w) V ms tape rl.slot = .running zs := hz
  change ZkState.built sys = zkInputBind c.nl w V (V.closeOf (ms rl.slot))
    (tape rl.index) (tapeState (w := w) V ms tape rl.slot) at hstep
  rw [hz', zkInputBind] at hstep
  split_ifs at hstep
  exact ZkState.built.inj hstep

omit [DecidableEq F] in
/-- The successful build's satisfying assignment also passes the actual input binding. -/
theorem input_check_of_running_zkBuilt (tape : RawTape) {zs : ZkRunning M L 0 F}
    (hz : tapeState (w := w) V ms tape (Rounds.Role.layerBase w c.nl) = .running zs)
    {sys : LigeroSystem c.ninp M F} (hBuilt : zkBuilt (w := w) V ms tape = some sys)
    (wcol : Fin c.ninp → F) (pad : Pad M F) (hSat : sys.Sat wcol pad) :
    let rl := (Rounds.Role.inputBind : Role)
    let cm := V.closeOf (ms rl.slot)
    let a := V.decodeF (tape rl.index)
    ligero_input_row V.npub wcol pad (V.inCoeffs zs.bound a) (V.pubBinding zs.bound a)
      (cm.wc0 + a * cm.wc1) a cm.dwL cm.dwR := by
  have he := inputSystem_eq_of_running_zkBuilt V ms tape hz hBuilt
  dsimp only at he
  rw [he, inputSystem, buildSystemMulti_Sat] at hSat
  exact hSat.2

omit x in
include hV hst0 in
/-- The fixed hash-side message schedule has one degree-81 system for every evaluation
of the symbolic ordinary challenges. -/
theorem FieldTape.exists_v7_system (hpos : 0 < c.nl)
    (hlin : c.nl + 1 ≤ V.nlin) (hquad : c.nl ≤ V.nt)
    {R : CertifiedV1.Row} (hR : V7HashProfile R)
    (hnl : c.nl = R.params.nl) (hw : w = R.params.rounds) (hlogv : logv ≤ 5)
    (hP : P.Bounded) (raw : (σ → F) → RawTape) (hraw : ∀ a, P.Matches V a (raw a)) :
    ∃ S : System σ F c.ninp M, S.Bounded 81 ∧
      ∀ a, zkBuilt (w := w) V ms (raw a) = some (S.eval a) := by
  exact ⟨P.system V ms pub hpos, P.system_bounded81 V ms pub hpos hR hnl hw hlogv hP,
    fun a => FieldTape.zkBuilt_eq V ms P hV hst0 a (raw a) (hraw a) hpos hlin hquad⟩

end Run

end LfzkV1.ResidualReplay125
