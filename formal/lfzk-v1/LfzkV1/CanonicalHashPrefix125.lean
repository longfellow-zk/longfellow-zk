import LfzkV1.HashFieldPath125
import LfzkV1.CanonicalOpening125
import LfzkV1.CompiledZkDeployedHash

/-! A canonical hash-side prefix is determined by the fields the verifier absorbs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CanonicalHashPrefix125

open LfzkV1.RbrZkLongfellow LfzkV1.HashFieldPath125 LfzkV1.ZkArithProfile
open LfzkV1.Arith LfzkV1.ResidualReplay125
open LfzkV1.CompiledZk LfzkV1.CompiledZkDeployedHash LfzkV1.NizkZk
open LfzkV1.NizkDeployedHash LfzkV1.NizkGrinding LfzkV1.CanonicalOpening125
open Bcs.TotalOracle

variable {C F X Q Msg Gpt Lift : Type} [Field F]
variable {M ninp L logc nl : ℕ} {w : ℕ → ℕ}

/-- The absorbed field payload at a field slot or the fixed batch marker.
The opening response has its own encoding and is handled separately. -/
def payload (V : ZkCode C F X Q Msg Gpt M ninp L logc)
    (role : Rounds.Role nl w) (msg : Msg) : Option (F × F) :=
  match role with
  | .layerPair ly => if ly.val = 0 then none else some ((V.closeOf msg).wc0, (V.closeOf msg).wc1)
  | .sumcheck _ _ => some ((V.roundOf msg).tr0, (V.roundOf msg).tr2)
  | .inputBind => some ((V.closeOf msg).wc0, (V.closeOf msg).wc1)
  | .ligeroChallenge | .ligeroQuery => none

/-- The transcript carrier represents exactly the serialized fields at each
slot. The pad indices used by the verifier are fixed by the circuit schedule. -/
structure FieldMessages (V : ZkCode C F X Q Msg Gpt M ninp L logc) (nl : ℕ) (w : ℕ → ℕ) where
  valid : Rounds.Role nl w → Msg → Prop
  eq_of_payload_eq : ∀ role : Rounds.Role nl w, role ≠ .ligeroQuery →
    ∀ {a b}, valid role a → valid role b → payload V role a = payload V role b → a = b
  round_pads : ∀ (ly : Fin nl) (j : Fin (w ly.val)) {a b},
    valid (.sumcheck ly j) a → valid (.sumcheck ly j) b →
    (V.roundOf a).pp0 = (V.roundOf b).pp0 ∧ (V.roundOf a).pp2 = (V.roundOf b).pp2
  close_pads : ∀ role : Rounds.Role nl w,
    (role = .inputBind ∨ ∃ ly : Fin nl, ly.val ≠ 0 ∧ role = .layerPair ly) →
    ∀ {a b}, valid role a → valid role b →
    (V.closeOf a).dwL = (V.closeOf b).dwL ∧ (V.closeOf a).dwR = (V.closeOf b).dwR

variable [SumcheckV1Interp F]
variable {V : ZkCode C F X Q Msg Gpt M ninp L logc}
variable {H : ZkHonest F Lift L logc}

theorem round_unique (wire : FieldMessages V nl w) (ly : Fin nl) (j : Fin (w ly.val))
    (lift : Lift) (pad : Pad M F) (zs : ZkRunning M L logc F) {a b : Msg}
    (ha : wire.valid (.sumcheck ly j) a) (hb : wire.valid (.sumcheck ly j) b)
    (hca : RoundCanonical H lift pad zs (V.roundOf a))
    (hcb : RoundCanonical H lift pad zs (V.roundOf b)) : a = b := by
  apply wire.eq_of_payload_eq (.sumcheck ly j) (by simp) ha hb
  obtain ⟨h0, h2⟩ := wire.round_pads ly j ha hb
  unfold RoundCanonical at hca hcb
  simp only [payload, hca, hcb, h0, h2]

variable [Fintype F] [DecidableEq F]

omit [SumcheckV1Interp F] in
theorem close_unique {c : QuadCircuit F} {logv : ℕ}
    {code : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0}
    {pub : Fin c.ninp → F} (hcode : CodeAgreesP c pub L code)
    {honest : ZkHonest F Lift L 0} {assignment : Lift → LigeroAssignment c.ninp M F}
    (boundary : ZkBoundary code honest assignment c.nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : boundary.W = zkWP pub wOf)
    (wire : FieldMessages code c.nl w) (role : Rounds.Role c.nl w)
    (hrole : role = .inputBind ∨ ∃ ly : Fin c.nl, ly.val ≠ 0 ∧ role = .layerPair ly)
    (lift : Lift) (zs : ZkRunning M L 0 F) {a b : Msg}
    (ha : wire.valid role a) (hb : wire.valid role b)
    (hca : CloseCanonical boundary lift zs (code.closeOf a))
    (hcb : CloseCanonical boundary lift zs (code.closeOf b)) : a = b := by
  obtain ⟨hL, hR⟩ := wire.close_pads role hrole ha hb
  have hpair := (closeFields_profiled code hcode boundary wOf hW lift zs (code.closeOf a) hca).trans
    (by simpa only [hL, hR] using
      (closeFields_profiled code hcode boundary wOf hW lift zs (code.closeOf b) hcb).symm)
  rcases hrole with rfl | ⟨ly, hn, rfl⟩
  · exact wire.eq_of_payload_eq .inputBind (by simp) ha hb (congrArg some hpair)
  · exact wire.eq_of_payload_eq (.layerPair ly) (by simp) ha hb
      (by simpa only [payload, if_neg hn] using congrArg some hpair)

section Uniqueness

variable {Ctx : Type} [Inhabited Msg] {c : QuadCircuit F} {logv : ℕ}
variable {code : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0}
variable {pub : Fin c.ninp → F}
variable {honest : ZkHonest F Lift L 0} {assignment : Lift → LigeroAssignment c.ninp M F}

local notation "Role" => Rounds.Role c.nl w
local notation "Point" => MPoint Ctx Msg c.nl w
local notation "Tape" => Fin (Rounds.Role.length c.nl w) → C

noncomputable def runTape (ctx : Ctx) (oracle : Point → C) (msgs : ℕ → Msg) : Tape :=
  fun j => oracle (msgPoint ctx (fun f i => f i) msgs j.val)

omit [Fintype F] [DecidableEq F] in
private theorem same_state (ctx : Ctx) (oracle : Point → C) (a b : ℕ → Msg)
    (j : ℕ) (hj : j ≤ Rounds.Role.length c.nl w) (hm : ∀ i < j, a i = b i) :
    tapeState (w := w) code a (runTape ctx oracle a) j =
      tapeState (w := w) code b (runTape ctx oracle b) j := by
  rw [tapeState_eq code a _ hj, tapeState_eq code b _ hj]
  have ht : Bcs.trunc (runTape ctx oracle a) j hj = Bcs.trunc (runTape ctx oracle b) j hj := by
    funext i
    exact congrArg oracle (msgPoint_eq_of_prefix ctx (fun k hk => hm k (hk.trans_lt i.isLt)))
  exact (state_congrG (zkRun_msgLocal code (fun _ _ _ _ => ∅)) j hm _).trans
    (congrArg ((zkRun (nl := c.nl) (w := w) code b (fun _ _ _ _ => ∅)).state j) ht)

/-- On one oracle, a fixed lift and initial context determine all messages
before the opening point. The field roles use their actual running states. -/
theorem canonical_prefix_eq (hpos : 0 < c.nl) (hcode : CodeAgreesP c pub L code)
    (hst0 : ∀ G, (code.st0 G).g0 = padG L G ∧ (code.st0 G).g1 = padG L G)
    (boundary : ZkBoundary code honest assignment c.nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : boundary.W = zkWP pub wOf) (wire : FieldMessages code c.nl w)
    (ctx : Ctx) (oracle : Point → C) (lift : Lift) (a b : ℕ → Msg)
    (ha : ∀ role : Role, wire.valid role (a role.slot))
    (hb : ∀ role : Role, wire.valid role (b role.slot))
    (ca : CanonicalRun code a boundary lift (runTape ctx oracle a))
    (cb : CanonicalRun code b boundary lift (runTape ctx oracle b)) :
    ∀ j < (Rounds.Role.ligeroQuery : Role).slot, a j = b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    let role : Role := roleAt j
    have hlen : j < Rounds.Role.length c.nl w := hj.trans (Rounds.Role.slot_lt _)
    have hr : role.slot = j := slot_roleAt hlen
    have hprefix : ∀ i < j, a i = b i := fun i hi => ih i hi (hi.trans hj)
    have hsame : tapeState (w := w) code a (runTape ctx oracle a) role.slot =
        tapeState (w := w) code b (runTape ctx oracle b) role.slot := by
      rw [hr]
      exact same_state (code := code) ctx oracle a b j hlen.le hprefix
    have hj' : role.slot < (Rounds.Role.ligeroQuery : Role).slot := by rw [hr]; exact hj
    rw [← hr]
    have hA := ha role
    have hB := hb role
    clear ha hb hprefix ih
    generalize hrole : role = r at hA hB hsame hj' ⊢
    cases r with
    | sumcheck ly k =>
      obtain ⟨zs, hz⟩ := tapeState_running code a hcode hst0 (runTape ctx oracle a) ly k.val k.isLt.le
      change tapeState (w := w) code a (runTape ctx oracle a)
        (Rounds.Role.sumcheck ly k).slot = .running zs at hz
      exact round_unique wire ly k lift (assignment lift).2 zs hA hB
        (ca.round ly k zs hz) (cb.round ly k zs (hsame.symm.trans hz))
    | layerPair ly =>
      by_cases hzero : ly.val = 0
      · exact wire.eq_of_payload_eq (.layerPair ly) (by simp) hA hB (by simp [payload, hzero])
      · let prev : Fin c.nl := ⟨ly.val - 1, by have := ly.isLt; omega⟩
        have hprev : prev.val + 1 = ly.val := by dsimp [prev]; omega
        have hnext : prev.val + 1 < c.nl := by rw [hprev]; exact ly.isLt
        have hly : (⟨prev.val + 1, hnext⟩ : Fin c.nl) = ly := Fin.ext hprev
        have hbase : Rounds.Role.layerBase w prev.val + 1 + w prev.val =
            (Rounds.Role.layerPair (w := w) ly).slot := by
          change _ = Rounds.Role.layerBase w ly.val
          calc
            _ = Rounds.Role.layerBase w (prev.val + 1) := by rw [Rounds.Role.layerBase_succ]; omega
            _ = _ := congrArg (Rounds.Role.layerBase w) hprev
        obtain ⟨zs, hz⟩ := tapeState_running code a hcode hst0 (runTape ctx oracle a)
          prev (w prev.val) le_rfl
        have hy := hsame.symm.trans (hbase ▸ hz)
        apply close_unique hcode boundary wOf hW wire (.layerPair ly)
          (Or.inr ⟨ly, hzero, rfl⟩) lift zs hA hB
        · simpa only [closeMsg, dif_pos hnext, pairMsg, hly] using ca.close prev zs hz
        · simpa only [closeMsg, dif_pos hnext, pairMsg, hly] using cb.close prev zs (hbase.symm ▸ hy)
    | inputBind =>
      let last : Fin c.nl := ⟨c.nl - 1, by omega⟩
      have hlast : last.val + 1 = c.nl := by dsimp [last]; omega
      have hnot : ¬ last.val + 1 < c.nl := by omega
      have hbase : Rounds.Role.layerBase w last.val + 1 + w last.val =
          (Rounds.Role.inputBind : Role).slot := by
        change _ = Rounds.Role.layerBase w c.nl
        calc
          _ = Rounds.Role.layerBase w (last.val + 1) := by rw [Rounds.Role.layerBase_succ]; omega
          _ = _ := congrArg (Rounds.Role.layerBase w) hlast
      obtain ⟨zs, hz⟩ := tapeState_running code a hcode hst0 (runTape ctx oracle a)
        last (w last.val) le_rfl
      have hy := hsame.symm.trans (hbase ▸ hz)
      exact close_unique hcode boundary wOf hW wire .inputBind (Or.inl rfl) lift zs hA hB
        (by simpa only [closeMsg, dif_neg hnot] using ca.close last zs hz)
        (by simpa only [closeMsg, dif_neg hnot] using cb.close last zs (hbase.symm ▸ hy))
    | ligeroChallenge => exact wire.eq_of_payload_eq .ligeroChallenge (by simp) hA hB rfl
    | ligeroQuery => exact (Nat.lt_irrefl _ hj').elim

/-- If a fixed batch and statement allow at most one response message,
the canonical field run determines a single opening input on this oracle. -/
theorem canonical_opening_unique (hpos : 0 < c.nl) (hcode : CodeAgreesP c pub L code)
    (hst0 : ∀ G, (code.st0 G).g0 = padG L G ∧ (code.st0 G).g1 = padG L G)
    (boundary : ZkBoundary code honest assignment c.nl w) (wOf : Lift → Fin c.ninp → F)
    (hW : boundary.W = zkWP pub wOf) (wire : FieldMessages code c.nl w)
    (ctx : Ctx) (oracle : Point → C) (lift : Lift) (a b : ℕ → Msg)
    (ha : ∀ role : Role, wire.valid role (a role.slot))
    (hb : ∀ role : Role, wire.valid role (b role.slot))
    (ca : CanonicalRun code a boundary lift (runTape ctx oracle a))
    (cb : CanonicalRun code b boundary lift (runTape ctx oracle b))
    (replyOK : Option (LigeroSystem c.ninp M F) → X → Msg → Prop)
    (replyUnique : ∀ sys x {m m'}, replyOK sys x m → replyOK sys x m' → m = m')
    (hA : replyOK (zkBuilt (w := w) code a (runTape ctx oracle a))
      (code.decodeChal (runTape ctx oracle a (Rounds.Role.ligeroChallenge : Role).index))
      (a (Rounds.Role.ligeroQuery : Role).slot))
    (hB : replyOK (zkBuilt (w := w) code b (runTape ctx oracle b))
      (code.decodeChal (runTape ctx oracle b (Rounds.Role.ligeroChallenge : Role).index))
      (b (Rounds.Role.ligeroQuery : Role).slot)) :
    msgPoint ctx (fun f i => f i) a (Rounds.Role.ligeroQuery : Role).slot =
      (msgPoint ctx (fun f i => f i) b (Rounds.Role.ligeroQuery : Role).slot : Point) := by
  have hpref := canonical_prefix_eq hpos hcode hst0 boundary wOf hW wire ctx oracle lift a b ha hb ca cb
  let k := (Rounds.Role.ligeroChallenge : Role).slot
  have hk : k < (Rounds.Role.ligeroQuery : Role).slot := by simp [k, Rounds.Role.slot]
  have hbld : zkBuilt (w := w) code a (runTape ctx oracle a) =
      zkBuilt (w := w) code b (runTape ctx oracle b) := by
    have hs := same_state (code := code) ctx oracle a b k (Rounds.Role.slot_lt _).le
      (fun i hi => hpref i (hi.trans hk))
    have hlen : k ≤ Rounds.Role.length c.nl w := (Rounds.Role.slot_lt _).le
    rw [tapeState_eq code a _ hlen, tapeState_eq code b _ hlen] at hs
    exact congrArg builtOf hs
  have hbatch : runTape ctx oracle a (Rounds.Role.ligeroChallenge : Role).index =
      runTape ctx oracle b (Rounds.Role.ligeroChallenge : Role).index :=
    congrArg oracle (msgPoint_eq_of_prefix ctx (fun i hi => hpref i (hi.trans_lt hk)))
  rw [hbld, hbatch] at hA
  have hrepl := replyUnique _ _ hA hB
  apply msgPoint_eq_of_prefix
  intro i hi
  rcases lt_or_eq_of_le hi with hlt | heq
  · exact hpref _ hlt
  · simpa only [heq] using hrepl

omit [Field F] [SumcheckV1Interp F] [Fintype F] [DecidableEq F] in
private theorem tapePrefix_off_opening (ctx : Ctx) (msgs : ℕ → Msg)
    (opening : Point) (hrole : opening.role = .ligeroQuery) {H H' : Point → C}
    (hoff : AgreeOff opening H H') (i : Fin (Rounds.Role.length c.nl w))
    (hi : i.val < (Rounds.Role.ligeroQuery : Role).slot) :
    runTape ctx H msgs i = runTape ctx H' msgs i := by
  apply hoff
  intro he
  let addr : Point := msgPoint ctx (fun f j => f j) msgs i.val
  have haddr : addr.role.slot = i.val := slot_msgPoint ctx (fun f j => f j) msgs i.isLt
  have heq := (congrArg (fun p : Point => p.role.slot) he).trans
    (congrArg (fun r : Role => r.slot) hrole)
  exact (Nat.ne_of_lt hi) (haddr.symm.trans heq)

omit [Fintype F] [DecidableEq F] in
private theorem state_off_opening (ctx : Ctx) (msgs : ℕ → Msg)
    (opening : Point) (hrole : opening.role = .ligeroQuery) {H H' : Point → C}
    (hoff : AgreeOff opening H H') (j : ℕ) (hj : j ≤ (Rounds.Role.ligeroQuery : Role).slot) :
    tapeState (w := w) code msgs (runTape ctx H msgs) j =
      tapeState (w := w) code msgs (runTape ctx H' msgs) j := by
  have hlt : j ≤ Rounds.Role.length c.nl w := hj.trans (Rounds.Role.slot_lt _).le
  rw [tapeState_eq code msgs _ hlt, tapeState_eq code msgs _ hlt]
  congr 1
  funext i
  exact tapePrefix_off_opening ctx msgs opening hrole hoff ⟨i.val, i.isLt.trans_le hlt⟩
    (i.isLt.trans_le hj)

omit [Fintype F] [DecidableEq F] in
theorem built_batch_off_opening (ctx : Ctx) (msgs : ℕ → Msg)
    (opening : Point) (hrole : opening.role = .ligeroQuery) {H H' : Point → C}
    (hoff : AgreeOff opening H H') :
    zkBuilt (w := w) code msgs (runTape ctx H msgs) =
      zkBuilt (w := w) code msgs (runTape ctx H' msgs) ∧
    runTape ctx H msgs (Rounds.Role.ligeroChallenge : Role).index =
      runTape ctx H' msgs (Rounds.Role.ligeroChallenge : Role).index := by
  let batch := (Rounds.Role.ligeroChallenge : Role).slot
  have hb : batch < (Rounds.Role.ligeroQuery : Role).slot := by simp [batch, Rounds.Role.slot]
  have hs := state_off_opening (code := code) ctx msgs opening hrole hoff batch hb.le
  have hlen : batch ≤ Rounds.Role.length c.nl w := (Rounds.Role.slot_lt _).le
  rw [tapeState_eq code msgs _ hlen, tapeState_eq code msgs _ hlen] at hs
  exact ⟨congrArg builtOf hs, tapePrefix_off_opening ctx msgs opening hrole hoff _ hb⟩

omit [DecidableEq F] in
/-- Reprogramming any opening input cannot affect the field run or its
canonical messages. -/
theorem canonical_run_off_opening
    (boundary : ZkBoundary code honest assignment c.nl w) (lift : Lift) (ctx : Ctx)
    (msgs : ℕ → Msg) (opening : Point) (hrole : opening.role = .ligeroQuery)
    {H H' : Point → C} (hoff : AgreeOff opening H H') :
    CanonicalRun code msgs boundary lift (runTape ctx H msgs) ↔
      CanonicalRun code msgs boundary lift (runTape ctx H' msgs) := by
  let last := (Rounds.Role.ligeroQuery : Role).slot
  have hstate := state_off_opening (code := code) ctx msgs opening hrole hoff
  have hinit : Rounds.Role.layerBase w 0 + 1 ≤ last := by
    simp [last, Rounds.Role.slot, Rounds.Role.layerBase]
  have hround (ly : Fin c.nl) (k : Fin (w ly.val)) : (Rounds.Role.sumcheck ly k).slot ≤ last := by
    have hj := k.isLt
    have hlt : (Rounds.Role.sumcheck ly k).slot < Rounds.Role.layerBase w (ly.val + 1) := by
      rw [Rounds.Role.layerBase_succ, Rounds.Role.slot]
      omega
    exact (hlt.le.trans (Rounds.Role.layerBase_mono (Nat.succ_le_of_lt ly.isLt))).trans
      (Nat.le_add_right _ _)
  have hclose (ly : Fin c.nl) : Rounds.Role.layerBase w ly.val + 1 + w ly.val ≤ last := by
    have hm := Rounds.Role.layerBase_mono (w := w) (Nat.succ_le_of_lt ly.isLt)
    rw [Rounds.Role.layerBase_succ] at hm
    change _ ≤ Rounds.Role.layerBase w c.nl + 2
    omega
  constructor <;> intro path
  · obtain ⟨zs, hz, hr⟩ := path.initial
    exact {
      initial := ⟨zs, (hstate _ hinit).symm.trans hz, hr⟩
      round := fun ly k zs hz => path.round ly k zs ((hstate _ (hround ly k)).trans hz)
      close := fun ly zs hz => path.close ly zs ((hstate _ (hclose ly)).trans hz) }
  · obtain ⟨zs, hz, hr⟩ := path.initial
    exact {
      initial := ⟨zs, (hstate _ hinit).trans hz, hr⟩
      round := fun ly k zs hz => path.round ly k zs ((hstate _ (hround ly k)).symm.trans hz)
      close := fun ly zs hz => path.close ly zs ((hstate _ (hclose ly)).symm.trans hz) }

end Uniqueness

end LfzkV1.CanonicalHashPrefix125
