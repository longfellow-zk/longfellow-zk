import LfzkV2.Current.ZeroKnowledge.FrontendWriteLog
import LfzkV2.Current.RuntimeRoles

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
  snapshots_roles body side _ (fun role member => RuntimeRoles.frontend_side side _ role member)

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

end LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
