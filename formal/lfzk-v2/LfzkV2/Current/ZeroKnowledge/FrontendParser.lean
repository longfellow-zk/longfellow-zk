import LfzkV2.Current.ApplicationViewReplay
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptWire

/-! Required frontend fields are recovered from the actual canonical
query history. These readback facts hold independently of the simulator's
state correspondence and before any verifier-acceptance assumption. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Parser
open SumcheckV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount) (initial : Digest)
local notation "Encoding" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
variable (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
variable (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)

theorem readAt {X : Type} (n : ℕ) (bounded : n ≤ g.roles.length)
    (i : Fin g.roles.length) (past : i.val ≤ n)
    (read : ProtocolWrites.Fresh g fields Advice → Option X) :
    (((Encoding).chain initial).point proof H n).readAt i.val (read ∘ Prod.snd) =
      read (ProtocolWrites.fresh proof.body i) := by
  rw [Replay.Encoding.readAt_replay _ _ _ _ _ bounded i past]
  exact congrArg read (CanonicalRequest.block_fresh repr shape setup publicCount binaryRequest metadata request proof i _)

theorem strictAnswer (n : ℕ) (bounded : n ≤ g.roles.length) (q : ℕ) (past : q<n) :
    ApplicationPrefix.strictAnswer (((Encoding).chain initial).point proof H n)
      ((((Encoding).chain initial).point proof H n).priorAnswers H) q =
        some (H (((Encoding).chain initial).point proof H q)).2 :=
  ApplicationViewReplay.strictAnswer_replay Encoding initial proof H n q bounded past

theorem read_mu (n : ℕ) (bounded : n ≤ g.roles.length)
    (past : ApplicationPrefix.conversionIndex g ≤ n) :
    (((Encoding).chain initial).point proof H n).readAt (ApplicationPrefix.conversionIndex g)
      (fun block => block.2.mu) = some proof.body.mu := by
  have bound : ApplicationPrefix.conversionIndex g < g.roles.length := by
    have length := g.roles_length
    simp only [ApplicationPrefix.conversionIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart]
    omega
  let i : Fin g.roles.length := ⟨ApplicationPrefix.conversionIndex g,bound⟩
  have role : g.roles.get i = .conversion := by
    have hr := RuntimeRoles.adapter_get g (2 : Fin 3)
    exact Option.some.inj ((List.getElem?_eq_getElem (l := g.roles) bound).symm.trans hr)
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded i past (fun fresh => fresh.mu)]
  simp only [ProtocolWrites.fresh,role,↓reduceIte]

theorem read_fingerprints (n : ℕ) (bounded : n ≤ g.roles.length) (past : g.primeStart ≤ n) :
    (((Encoding).chain initial).point proof H n).readAt g.primeStart
      (fun block => block.2.fingerprints) = some proof.body.fingerprints := by
  have bound : g.primeStart < g.roles.length := by
    have length := g.roles_length
    simp only [Geometry.primeStart]
    omega
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded
    ⟨g.primeStart,bound⟩ past (fun fresh => fresh.fingerprints)]
  simp only [ProtocolWrites.fresh,↓reduceIte]

theorem read_advice (n : ℕ) (bounded : n ≤ g.roles.length) (past : g.binaryStart ≤ n) :
    (((Encoding).chain initial).point proof H n).readAt g.binaryStart
      (fun block => block.2.advice) = some proof.body.advice := by
  have bound : g.binaryStart < g.roles.length := by
    have length := g.roles_length
    simp only [Geometry.binaryStart]
    omega
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded ⟨g.binaryStart,bound⟩ past (fun fresh => fresh.advice)]
  simp only [ProtocolWrites.fresh,↓reduceIte]

theorem read_packingU (n : ℕ) (bounded : n ≤ g.roles.length)
    (nontrivial : g.packingDegree ≠ 1) (past : ApplicationPrefix.packingIndex g ≤ n) :
    (((Encoding).chain initial).point proof H n).readAt (ApplicationPrefix.packingIndex g)
      (fun block => block.2.packingU) = (ProtocolWrites.packingPair proof.body).map Prod.fst := by
  have bound : ApplicationPrefix.packingIndex g < g.roles.length := by
    have length := g.roles_length
    simp only [ApplicationPrefix.packingIndex,Geometry.binaryStart]
    omega
  let i : Fin g.roles.length := ⟨ApplicationPrefix.packingIndex g,bound⟩
  have role : g.roles.get i = .packing :=
    Option.some.inj ((List.getElem?_eq_getElem (l := g.roles) bound).symm.trans (RuntimeRoles.packing_get g nontrivial))
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded i past (fun fresh => fresh.packingU)]
  simp only [ProtocolWrites.fresh,role,↓reduceIte]

theorem read_packingA (n : ℕ) (bounded : n ≤ g.roles.length) (past : g.batchingIndex.val ≤ n) :
    (((Encoding).chain initial).point proof H n).readAt g.batchingIndex.val
      (fun block => block.2.packingA) = (ProtocolWrites.packingPair proof.body).map Prod.snd := by
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded g.batchingIndex past (fun fresh => fresh.packingA)]
  simp only [ProtocolWrites.fresh,g.get_batchingIndex,↓reduceIte]

theorem mapMessage_id {E : Type} (message : Layered.Replay.Message E) :
    ApplicationPrefix.mapMessage id message = message := by cases message <;> rfl

theorem prime_wire (n : ℕ) (bounded : n ≤ g.roles.length)
    (q : Fin (g.prime.roles .prime).length) (past : g.primeStart+q.val ≤ n) :
    ApplicationPrefix.wire (((Encoding).chain initial).point proof H n) .prime id g.primeStart q.val =
      some ((Prefix.roleWrite proof.body.prime ((g.prime.roles .prime).get q)).getD .empty) := by
  unfold ApplicationPrefix.wire
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded
    (g.primeIndex q) past (fun fresh => some (ApplicationPrefix.mapMessage id (fresh.frontend .prime)))]
  rw [ProtocolWrites.fresh,g.prime_role_get]
  exact congrArg some ((mapMessage_id _).trans (Prefix.role_message proof.body .prime _
    (RuntimeRoles.frontend_side .prime g.prime _ (List.get_mem _ q))).symm)

theorem binary_wire (n : ℕ) (bounded : n ≤ g.roles.length)
    (q : Fin (g.binary.roles .binary).length) (past : g.binaryStart+q.val ≤ n) :
    ApplicationPrefix.wire (((Encoding).chain initial).point proof H n) .binary id g.binaryStart q.val =
      some ((Prefix.roleWrite proof.body.binary ((g.binary.roles .binary).get q)).getD .empty) := by
  unfold ApplicationPrefix.wire
  erw [readAt repr shape setup publicCount binaryRequest metadata request initial proof H n bounded
    (g.binaryIndex q) past (fun fresh => some (ApplicationPrefix.mapMessage id (fresh.frontend .binary)))]
  rw [ProtocolWrites.fresh,g.binary_role_get]
  exact congrArg some ((mapMessage_id _).trans (Prefix.role_message proof.body .binary _
    (RuntimeRoles.frontend_side .binary g.binary _ (List.get_mem _ q))).symm)

theorem role_stream_cast {E : Type} (first second : Frontend) (same : first = second)
    (side : Side) (body : FrontendPayload E first) :
    (first.roles side).map (Prefix.roleWrite body) =
      (second.roles side).map (Prefix.roleWrite (Eq.mp (congrArg (FrontendPayload E) same) body)) := by
  subst second
  rfl

def start (g : Geometry) : Side → ℕ
  | .binary => g.binaryStart
  | .prime => g.primeStart

theorem frontend_wire (side : Side) (n : ℕ) (bounded : n ≤ g.roles.length)
    (q : Fin ((g.frontend side).roles side).length) (past : start g side+q.val ≤ n) :
    ApplicationPrefix.wire (((Encoding).chain initial).point proof H n) side id (start g side) q.val =
      some ((Prefix.roleWrite (proof.body.frontend side) (((g.frontend side).roles side).get q)).getD .empty) := by
  cases side
  · exact binary_wire repr shape setup publicCount binaryRequest metadata request initial proof H n bounded q past
  · exact prime_wire repr shape setup publicCount binaryRequest metadata request initial proof H n bounded q past

section Participant
variable (side : Side)
variable {out input : ℕ} {circuit : Layered.Circuit (fields side) out input}
variable (plan : FrontendSchedule.Plan (fields side) circuit) (shapeEq : g.frontend side = plan.frontend)

def payload : Layered.Replay.Payload circuit :=
  (CompleteShape.bodyEquiv plan).symm (Eq.mp (congrArg (FrontendPayload (fields side)) shapeEq) (proof.body.frontend side))

theorem messages (n : ℕ) (bounded : n ≤ g.roles.length)
    (past : start g side+FrontendReplay.slots circuit ≤ n) :
    ApplicationPrefix.Messages.read circuit
      (ApplicationPrefix.wire (((Encoding).chain initial).point proof H n) side id (start g side)) =
        some (payload proof side plan shapeEq) := by
  let decoded := payload proof side plan shapeEq
  have encoded : Eq.mp (congrArg (FrontendPayload (fields side)) shapeEq) (proof.body.frontend side) =
      CompleteShape.bodyEquiv plan decoded := (CompleteShape.bodyEquiv plan).apply_symm_apply _ |>.symm
  have stream := role_stream_cast (g.frontend side) plan.frontend shapeEq side (proof.body.frontend side)
  rw [encoded,← Prefix.circuit_roles] at stream
  unfold ApplicationPrefix.Messages.read
  rw [ApplicationPrefix.Messages.readFrom_congr circuit _
    (fun q => some (FrontendTranscript.write circuit decoded q)) 0 (by
      intro q _ upper
      have qlt : q < ((g.frontend side).roles side).length := by
        rw [shapeEq,← plan.slots_eq_roles_length side]
        omega
      let index : Fin ((g.frontend side).roles side).length := ⟨q,qlt⟩
      have actual := frontend_wire repr shape setup publicCount binaryRequest metadata request initial proof H side
        n bounded index (by change start g side+q ≤ n; omega)
      have slot := congrArg (fun items => (items[q]?).map (fun item => item.getD .empty)) stream
      simp only [List.getElem?_map,List.getElem?_eq_getElem qlt,Option.map_some] at slot
      exact actual.trans (slot.trans (Prefix.circuit_wire plan decoded q (by omega))))]
  exact ApplicationPrefix.Messages.read_write circuit decoded

end Participant

end LfzkV2.Current.ZeroKnowledge.Frontend.Parser
