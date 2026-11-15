import LfzkV2.Current.CanonicalRequest

/-! The deployed format's node bytes from public data and the fresh writes
so far, as the zero-knowledge simulator writes them: the role packet and
request metadata are assembled from the current fresh write, with public
defaults only for malformed prefixes. `canonicalBase_body` identifies the
honest image with `CanonicalRequest.block`. -/
noncomputable section
namespace LfzkV2.Current.LegacyNode
open SumcheckV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice Auth C : Type}
variable (shape : WireBlocks.Shape g fields) (defaultAdvice : Advice)

def polynomial {E : Type} (zero : E) : Layered.Replay.Message E → E × E
  | .round p => (p.c0,p.c1)
  | _ => (zero,zero)

def cross {E : Type} (zero : E) : Layered.Replay.Message E → E
  | .cross x => x
  | _ => zero

def claims {E : Type} (zero : E) : Layered.Replay.Message E → E × E
  | .claims a b => (a,b)
  | _ => (zero,zero)

def startFromFresh (fresh : ProtocolWrites.Fresh g fields Advice) :
    (start : WireBlocks.Start) → WireBlocks.StartMetadata shape start →
      WireBlocks.StartData (Advice := Advice) shape start
  | .none, _ => ()
  | .prime, metadata =>
      (fresh.fingerprints.getD ((shape.zero .binary,shape.zero .binary),
        (shape.zero .prime,shape.zero .prime)),metadata)
  | .binary, metadata => (fresh.advice.getD defaultAdvice,metadata)

def roleFromFresh (fresh : ProtocolWrites.Fresh g fields Advice) :
    (role : Role) → WireBlocks.RoleMetadata shape role → WireBlocks.RoleData shape role
  | .fingerprint, _ => ()
  | .inputAssertions .., _ => ⟨0,by decide⟩
  | .assertions _ stage .., _ => ⟨stage % 2^64,Nat.mod_lt _ (by decide)⟩
  | .sumcheck side .., _ => polynomial (shape.zero side) (fresh.frontend side)
  | .terminal side .., _ => cross (shape.zero side) (fresh.frontend side)
  | .combine side .., _ => claims (shape.zero side) (fresh.frontend side)
  | .rowBatching, _ => ()
  | .conversion, _ => fresh.mu.getD (shape.zero .prime)
  | .packing, metadata => (metadata,fresh.packingU.getD (fun _ => shape.zero .binary))
  | .batching, metadata =>
      (if h : g.packingDegree = 1 then (by simpa only [WireBlocks.PackingA,h,↓reduceIte] using ())
       else (by simpa only [WireBlocks.PackingA,h,↓reduceIte] using
          fresh.packingA.getD (shape.zero .binary)),metadata)
  | .opening, _ => fresh.responses.getD
      (⟨fun _ => shape.zero .binary,fun _ => shape.zero .binary⟩,
       ⟨fun _ => shape.zero .prime,fun _ => shape.zero .prime⟩)

def fromFresh (i : Fin g.roles.length) (fresh : ProtocolWrites.Fresh g fields Advice)
    (metadata : WireBlocks.Metadata shape i) : WireBlocks.Data (Advice := Advice) shape i :=
  (startFromFresh shape defaultAdvice fresh (WireBlocks.startAt g i) metadata.1,
    roleFromFresh shape fresh (g.roles.get i) metadata.2)

theorem startFromFresh_body_for (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (start : WireBlocks.Start) (hs : WireBlocks.startAt g i = start)
    (metadata : WireBlocks.StartMetadata shape start) :
    startFromFresh shape defaultAdvice (ProtocolWrites.fresh body i) start metadata =
      WireBlocks.startFromBody shape body start metadata := by
  cases start with
  | none => rfl
  | prime =>
      have hp : i.val = g.primeStart := by
        unfold WireBlocks.startAt at hs
        split_ifs at hs
        simp_all
      simp [startFromFresh,WireBlocks.startFromBody,ProtocolWrites.fresh,hp]
  | binary =>
      have hb : i.val = g.binaryStart := by
        unfold WireBlocks.startAt at hs
        split_ifs at hs
        simp_all
      simp [startFromFresh,WireBlocks.startFromBody,ProtocolWrites.fresh,hb]

theorem startFromFresh_body (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (metadata : WireBlocks.StartMetadata shape (WireBlocks.startAt g i)) :
    startFromFresh shape defaultAdvice (ProtocolWrites.fresh body i) (WireBlocks.startAt g i) metadata =
      WireBlocks.startFromBody shape body (WireBlocks.startAt g i) metadata :=
  startFromFresh_body_for shape defaultAdvice body i _ rfl metadata

theorem roleFromFresh_body_for (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (role : Role) (hr : g.roles.get i = role) (valid : WireBlocks.ValidRole g role)
    (metadata : WireBlocks.RoleMetadata shape role) :
    roleFromFresh shape (ProtocolWrites.fresh body i) role metadata =
      WireBlocks.roleFromBody shape body role valid metadata := by
  simp only [List.get_eq_getElem] at hr
  cases role with
  | sumcheck side stage round =>
      obtain ⟨hs,hn⟩ := valid
      simp only [List.get_eq_getElem] at hn
      simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,
        hs,hn,Body.frontend,polynomial]
  | terminal side stage =>
      change stage < (g.frontend side).stages.length at valid
      simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,valid,cross]
  | combine side stage entries fragments last =>
      change stage < (g.frontend side).stages.length at valid
      simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,valid,claims]
  | packing =>
      change g.packingDegree ≠ 1 at valid
      simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.packingPair,valid]
      rfl
  | batching =>
      by_cases hd : g.packingDegree = 1 <;>
        simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr,
          ProtocolWrites.packingPair,hd]
      rfl
  | _ => simp [roleFromFresh,WireBlocks.roleFromBody,ProtocolWrites.fresh,hr]

theorem roleFromFresh_body (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (metadata : WireBlocks.RoleMetadata shape (g.roles.get i)) :
    roleFromFresh shape (ProtocolWrites.fresh body i) (g.roles.get i) metadata =
      WireBlocks.roleFromBody shape body (g.roles.get i) (WireBlocks.role_valid g i) metadata :=
  roleFromFresh_body_for shape body i _ rfl _ metadata

theorem fromFresh_body (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (metadata : WireBlocks.Metadata shape i) :
    fromFresh shape defaultAdvice i (ProtocolWrites.fresh body i) metadata =
      WireBlocks.fromBody shape i body metadata :=
  Prod.ext (startFromFresh_body shape defaultAdvice body i metadata.1)
    (roleFromFresh_body shape body i metadata.2)

section Canonical
variable (repr : ProofBodyCodec.Representations fields Advice) (setup : FingerprintPrefix.Setup)
variable (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount) (root : Digest)

/-- The actual canonical boundary serializer, receiving the same public
metadata inputs as the verifier. It never reconstructs or guesses a witness. -/
def canonicalBase (i : Fin g.roles.length)
    (writes : Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) (past : Fin i.val → C) :
    CanonicalRequest.Base repr shape setup publicCount :=
  if i.val = 0 then
    ((QueryRuntime.Runtime.first repr shape setup publicCount).block
      (FingerprintPrefix.context request root)).1
  else
    ((QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
      (fromFresh shape defaultAdvice i (writes (Fin.last i.val))
        (WireBlocks.requestMetadata shape (binaryRequest request.publicBits) request.primeInputs i
          (metadata request i writes past)))).1

theorem canonicalBase_body
    (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (past : Fin i.val → C) :
    canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request
        proof.body.commitment i (CanonicalRequest.writes proof.body i) past =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).block proof i past).1 := by
  by_cases hz : i.val = 0
  · simp only [canonicalBase,hz,↓reduceIte]
    rw [CanonicalRequest.block_zero repr shape setup publicCount binaryRequest metadata request proof i hz past]
  · simp only [canonicalBase,hz,↓reduceIte]
    rw [CanonicalRequest.block_pos repr shape setup publicCount binaryRequest metadata request proof i hz past]
    have hl : CanonicalRequest.writes proof.body i (Fin.last i.val) = ProtocolWrites.fresh proof.body i := rfl
    rw [hl,fromFresh_body]
    rfl

end Canonical

end LfzkV2.Current.LegacyNode
