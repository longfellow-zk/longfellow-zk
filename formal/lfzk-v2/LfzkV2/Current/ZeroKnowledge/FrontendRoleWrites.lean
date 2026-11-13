import LfzkV2.Current.ZeroKnowledge.FrontendWriteLog
import LfzkV2.Current.RuntimeShape

/-! The flat optional-message stream has exactly the actual public roles.
Assertions carry no new frontend polynomial. In particular their `none`
entry leaves the initial pending fingerprint/advice write intact, while the
round, cross and claim entries carry the canonical body payload fields. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
open SumcheckV2
open scoped Classical
variable {F : Type}

def roleWrite {frontend : Frontend} (body : FrontendPayload F frontend) : Role → Option (Layered.Replay.Message F)
  | .sumcheck _ stage round => some (ProtocolWrites.stageMessage body stage (.round round))
  | .terminal _ stage => some (ProtocolWrites.stageMessage body stage .cross)
  | .combine _ stage _ => some (ProtocolWrites.stageMessage body stage .claims)
  | _ => none

def stageWrites (payload : FrontendBody.StagePayload F) : List (Option (Layered.Replay.Message F)) :=
  none :: layer (FrontendBody.layer id payload.2)

theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range n) f).symm

theorem stage_roles (frontend : Frontend) (body : FrontendPayload F frontend)
    (side : Side) (i : Fin frontend.stages.length) (inputs : List Entry) :
    ((frontend.stages.get i).roles side i.val inputs).map (roleWrite body) =
      stageWrites ⟨(frontend.stages.get i).rounds,body i⟩ := by
  simp only [Stage.roles,List.map_append,List.map_cons,List.map_nil,range_map,List.map_ofFn,
    Function.comp_def,roleWrite,stageWrites,layer,rounds,List.cons_append,List.nil_append]
  simp only [ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,
    Fin.isLt,↓reduceDIte,FrontendBody.layer,id_eq]

theorem roles_stream (frontend : Frontend) (body : FrontendPayload F frontend) (side : Side) :
    (frontend.roles side).map (roleWrite body) =
      if frontend.stages.isEmpty then [none] else
        (FrontendBody.stages frontend body).flatMap stageWrites := by
  unfold Frontend.roles
  split_ifs with empty
  · rfl
  · simp only [List.map_flatMap,FrontendBody.stages,List.flatMap_map]
    congr 1
    funext i
    exact stage_roles frontend body side i _

theorem circuit_writes {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (payload : Layered.Replay.Payload circuit) (continuing : Bool) :
    Prefix.circuit plan payload continuing =
      if FrontendReplay.hasLayers circuit || continuing then
        (FrontendBody.write circuit payload).flatMap stageWrites else [none] := by
  induction plan generalizing continuing with
  | input => cases continuing <;> rfl
  | inputEntry => cases continuing <;> rfl
  | layer _ tail ih =>
      simp only [Prefix.circuit,FrontendReplay.hasLayers,Bool.true_or,↓reduceIte,
        FrontendBody.write,List.flatMap_cons,ih,Bool.or_true,stageWrites]
      rfl
  | entryLayer _ _ _ tail ih =>
      simp only [Prefix.circuit,FrontendReplay.hasLayers,Bool.true_or,↓reduceIte,
        FrontendBody.write,List.flatMap_cons,ih,Bool.or_true,stageWrites]
      rfl

theorem circuit_roles {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (payload : Layered.Replay.Payload circuit) (side : Side) :
    Prefix.circuit plan payload false =
      (plan.frontend.roles side).map (roleWrite (CompleteShape.bodyEquiv plan payload)) := by
  rw [circuit_writes,roles_stream,CompleteShape.stages_bodyEquiv,plan.hasLayers_eq]
  cases plan.frontend.stages.isEmpty <;> rfl

theorem message_refl (message : Layered.Replay.Message F) :
    CompleteTranscript.mapMessage (Equiv.refl F).symm message = message := by
  cases message <;> rfl

variable {g : Geometry} {fields : Fields} {Advice Authentication : Type}

theorem role_snapshot (body : Body g fields Advice Authentication) (side : Side) (role : Role)
    (owned : frontendSide role = some side) :
    WriteLog.withMessage side (Equiv.refl (fields side)) {}
      (roleWrite (body.frontend side) role) =
      ({ frontend := ProtocolWrites.frontendMessages body role } : ProtocolWrites.Fresh g fields Advice) := by
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at owned
  all_goals subst side
  all_goals simp only [roleWrite,WriteLog.withMessage,message_refl,ProtocolWrites.frontendMessages]

theorem role_message (body : Body g fields Advice Authentication) (side : Side) (role : Role)
    (owned : frontendSide role = some side) :
    (roleWrite (body.frontend side) role).getD .empty = ProtocolWrites.frontendMessages body role side := by
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at owned
  all_goals subst side
  all_goals simp only [roleWrite,Option.getD_none,Option.getD_some,ProtocolWrites.frontendMessages,
    Function.update_self]

theorem snapshots_roles (body : Body g fields Advice Authentication) (side : Side) (roles : List Role)
    (owned : ∀ role ∈ roles, frontendSide role = some side) :
    WriteLog.snapshots side (Equiv.refl (fields side)) {}
      (roles.map (roleWrite (body.frontend side))) =
      roles.map (fun role => ({ frontend := ProtocolWrites.frontendMessages body role } : ProtocolWrites.Fresh g fields Advice)) := by
  induction roles with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons,WriteLog.snapshots]
      rw [role_snapshot body side head (owned head (by simp))]
      exact congrArg (List.cons _) (ih (fun role member => owned role (List.mem_cons_of_mem _ member)))

theorem snapshots_frontend (body : Body g fields Advice Authentication) (side : Side) :
    WriteLog.snapshots side (Equiv.refl (fields side)) {}
      (((g.frontend side).roles side).map (roleWrite (body.frontend side))) =
      ((g.frontend side).roles side).map
        (fun role => ({ frontend := ProtocolWrites.frontendMessages body role } : ProtocolWrites.Fresh g fields Advice)) :=
  snapshots_roles body side _ (fun role member => RuntimeShape.frontend_side side _ role member)

theorem snapshots_map {A : Type} (side : Side) (field : fields side ≃ F)
    (items : List A) (write : A → Option (Layered.Replay.Message F)) :
    WriteLog.snapshots side field ({} : ProtocolWrites.Fresh g fields Advice) (items.map write) =
      items.map (fun item => WriteLog.withMessage side field {} (write item)) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons,WriteLog.snapshots,ih]

theorem circuit_snapshots_pending (side : Side) (field : fields side ≃ F) {out input : ℕ}
    {circuit : Layered.Circuit F out input} (plan : FrontendSchedule.Plan F circuit)
    (payload : Layered.Replay.Payload circuit) (pending : ProtocolWrites.Fresh g fields Advice) :
    WriteLog.snapshots side field pending (Prefix.circuit plan payload false) =
      pending :: (WriteLog.snapshots side field {} (Prefix.circuit plan payload false)).tail := by
  cases plan <;> rfl

/-- Exact fresh writes, including the fingerprint/advice values already
pending at the first assertion. Every later entry is reconstructed solely
from the same stage and coefficient indices as the complete body encoder. -/
theorem circuit_snapshots (side : Side) (field : fields side ≃ F) {out input : ℕ}
    {circuit : Layered.Circuit F out input} (plan : FrontendSchedule.Plan F circuit)
    (payload : Layered.Replay.Payload circuit) (pending : ProtocolWrites.Fresh g fields Advice) :
    WriteLog.snapshots side field pending (Prefix.circuit plan payload false) =
      pending :: ((plan.frontend.roles side).map
        (fun role => WriteLog.withMessage side field {}
          (roleWrite (CompleteShape.bodyEquiv plan payload) role))).tail := by
  rw [circuit_snapshots_pending,circuit_roles plan payload side,snapshots_map]


/-! Readback of the optional role writes through the actual frontend writer. -/
variable [Field F]

omit [Field F] in
theorem writeFrom_before {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (start q : ℕ) (before : q ≤ start) :
    FrontendTranscript.writeFrom circuit payload start q = .empty := by
  induction circuit generalizing start with
  | input => rfl
  | entry _ _ _ ih => exact ih payload start before
  | @layer out mid input assertions body rest ih =>
      have round : ¬ (start+1 ≤ q ∧ q < start+1+mid) := by omega
      have cross : q ≠ start+1+mid := by omega
      have claims : q ≠ start+mid+2 := by omega
      simp only [FrontendTranscript.writeFrom,dif_neg round,cross,claims,↓reduceIte]
      apply ih
      split_ifs <;> omega

omit [Field F] in
theorem writeFrom_translate {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (start q shift : ℕ) :
    FrontendTranscript.writeFrom circuit payload (start+shift) (q+shift) =
      FrontendTranscript.writeFrom circuit payload start q := by
  induction circuit generalizing start q with
  | input => rfl
  | entry _ _ _ ih => exact ih payload start q
  | @layer out mid input assertions body rest ih =>
      by_cases round : start+1 ≤ q ∧ q < start+1+mid
      · have shifted : start+shift+1 ≤ q+shift ∧ q+shift < start+shift+1+mid := by omega
        simp only [FrontendTranscript.writeFrom,dif_pos round,dif_pos shifted]
        congr 2
        apply Fin.ext
        change q+shift-(start+shift+1) = q-(start+1)
        omega
      · have shifted : ¬ (start+shift+1 ≤ q+shift ∧ q+shift < start+shift+1+mid) := by omega
        simp only [FrontendTranscript.writeFrom,dif_neg round,dif_neg shifted]
        by_cases cross : q = start+1+mid
        · have shiftedCross : q+shift = start+shift+1+mid := by omega
          rw [if_pos cross,if_pos shiftedCross]
        · have shiftedCross : q+shift ≠ start+shift+1+mid := by omega
          rw [if_neg cross,if_neg shiftedCross]
          by_cases claims : q = start+mid+2
          · have shiftedClaims : q+shift = start+shift+mid+2 := by omega
            rw [if_pos claims,if_pos shiftedClaims]
          · have shiftedClaims : q+shift ≠ start+shift+mid+2 := by omega
            rw [if_neg claims,if_neg shiftedClaims]
            cases h : FrontendReplay.hasLayers rest <;>
              simpa [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
                ih payload.2 (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) q

omit [Field F] in
theorem circuit_continue {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body)
    (layers : FrontendReplay.hasLayers body = true) :
    Prefix.circuit plan payload true = Prefix.circuit plan payload false := by
  cases plan <;> try rfl
  all_goals simp only [FrontendReplay.hasLayers,Bool.false_eq_true] at layers

omit [Field F] in
theorem layer_wire {out mid input assertions : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
    (rest : Layered.Circuit F mid input) (tail : FrontendSchedule.Plan F rest)
    (payload : Layered.Replay.Payload (.layer assertions body rest))
    (induction : ∀ q, q < FrontendReplay.slots rest →
      ((Prefix.circuit tail payload.2 false)[q]?).map (fun item => item.getD .empty) =
        some (FrontendTranscript.write rest payload.2 q))
    (q : ℕ) (bound : q < FrontendReplay.slots (.layer assertions body rest)) :
    ((none :: layer payload.1 ++ Prefix.circuit tail payload.2 true)[q]?).map (fun item => item.getD .empty) =
      some (FrontendTranscript.write (.layer assertions body rest) payload q) := by
  cases q with
  | zero =>
      rw [List.cons_append,List.getElem?_cons_zero]
      rw [FrontendTranscript.write,writeFrom_before _ _ 0 0 (le_refl _)]
      rfl
  | succ q =>
      simp only [List.cons_append,List.getElem?_cons_succ,layer,rounds,List.append_assoc]
      by_cases round : q < mid
      · rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using round)]
        simp only [List.getElem?_ofFn,round,↓reduceDIte,Option.map_some,Option.getD_some]
        have inRound : 0+1 ≤ q+1 ∧ q+1 < 0+1+mid := by omega
        simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_pos inRound]
        congr 2
      · rw [List.getElem?_append_right (by simpa only [List.length_ofFn] using Nat.le_of_not_gt round)]
        simp only [List.length_ofFn]
        by_cases cross : q = mid
        · subst q
          simp only [Nat.sub_self,List.getElem?_cons_zero,Option.map_some,Option.getD_some]
          have notRound : ¬ (0+1 ≤ mid+1 ∧ mid+1 < 0+1+mid) := by omega
          have isCross : mid+1 = 0+1+mid := by omega
          simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,if_pos isCross]
        · by_cases claims : q = mid+1
          · subst q
            have index : mid+1-mid = 1 := by omega
            simp only [index,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.map_some,Option.getD_some]
            have notRound : ¬ (0+1 ≤ mid+1+1 ∧ mid+1+1 < 0+1+mid) := by omega
            have notCross : mid+1+1 ≠ 0+1+mid := by omega
            have isClaims : mid+1+1 = 0+mid+2 := by omega
            simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,
              if_neg notCross,if_pos isClaims]
          · have after : 2 ≤ q-mid := by omega
            simp only [List.getElem?_cons,if_neg (show q-mid ≠ 0 by omega),
              if_neg (show q-mid-1 ≠ 0 by omega),List.nil_append]
            have index : q-mid-1-1 = q-(mid+2) := by omega
            rw [index]
            by_cases layers : FrontendReplay.hasLayers rest = true
            · have restBound : q-(mid+2) < FrontendReplay.slots rest := by
                simp only [FrontendReplay.slots,layers,↓reduceIte] at bound
                omega
              rw [circuit_continue tail payload.2 layers,induction _ restBound]
              have notRound : ¬ (0+1 ≤ q+1 ∧ q+1 < 0+1+mid) := by omega
              have notCross : q+1 ≠ 0+1+mid := by omega
              have notClaims : q+1 ≠ 0+mid+2 := by omega
              simp only [FrontendTranscript.write,FrontendTranscript.writeFrom,dif_neg notRound,
                if_neg notCross,if_neg notClaims,layers,↓reduceIte]
              have shifted := writeFrom_translate rest payload.2 0 (q-(mid+2)) (mid+3)
              simp only [Nat.zero_add] at shifted
              rw [show q+1 = (q-(mid+2))+(mid+3) by omega]
              simpa only [Nat.zero_add] using congrArg some shifted.symm
            · simp only [FrontendReplay.slots,layers,Bool.false_eq_true,↓reduceIte] at bound
              omega

omit [Field F] in
theorem circuit_wire {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body)
    (q : ℕ) (bound : q < FrontendReplay.slots body) :
    ((Prefix.circuit plan payload false)[q]?).map (fun item => item.getD .empty) =
      some (FrontendTranscript.write body payload q) := by
  induction plan generalizing q with
  | input =>
      have zero : q = 0 := by simpa only [FrontendReplay.slots] using Nat.lt_one_iff.mp bound
      subst q
      rfl
  | inputEntry =>
      have zero : q = 0 := by simpa only [FrontendReplay.slots] using Nat.lt_one_iff.mp bound
      subst q
      rfl
  | layer _ tail ih => exact layer_wire _ _ tail payload (ih payload.2) q bound
  | entryLayer _ _ _ tail ih => exact layer_wire _ _ tail payload (ih payload.2) q bound

end LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
