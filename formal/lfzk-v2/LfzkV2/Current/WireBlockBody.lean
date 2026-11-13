import LfzkV2.Current.WireBlockPublic

/-! Construct every prover write from the actual complete body. Metadata
contains only the intervening public/derived binds. Stage and round indices
are justified by the public schedule itself, rather than by a supplied cache
correspondence or a proof-dependent shape certificate. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open ProtocolWrites SumcheckV2 Layered.Replay
open scoped Classical

private def FrontendValid (frontend : Frontend) (side : Side) : Role → Prop
  | .inputAssertions participant _ => participant = side
  | .assertions participant stage .. => participant = side ∧ stage < frontend.stages.length
  | .sumcheck participant stage round => participant = side ∧
      ∃ hs : stage < frontend.stages.length, round < (frontend.stages.get ⟨stage,hs⟩).rounds
  | .terminal participant stage | .combine participant stage _ =>
      participant = side ∧ stage < frontend.stages.length
  | _ => False

private theorem frontend_valid (frontend : Frontend) (side : Side) (role : Role)
    (h : role ∈ frontend.roles side) : FrontendValid frontend side role := by
  by_cases he : frontend.stages.isEmpty
  · simp only [Frontend.roles,he,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at h
    subst role
    rfl
  · simp only [Frontend.roles,he,Bool.false_eq_true,↓reduceIte,List.mem_flatMap] at h
    obtain ⟨i,_,hr⟩ := h
    simp only [Stage.roles,List.mem_append,List.mem_cons,List.mem_map,List.mem_range,
      List.not_mem_nil,or_false] at hr
    rcases hr with (rfl | ⟨round,hround,rfl⟩) | rfl | rfl
    · exact ⟨rfl,i.isLt⟩
    · exact ⟨rfl,i.isLt,hround⟩
    · exact ⟨rfl,i.isLt⟩
    · exact ⟨rfl,i.isLt⟩

def ValidRole (g : Geometry) : Role → Prop
  | .sumcheck side stage round =>
      ∃ hs : stage < (g.frontend side).stages.length,
        round < ((g.frontend side).stages.get ⟨stage,hs⟩).rounds
  | .terminal side stage | .combine side stage _ => stage < (g.frontend side).stages.length
  | .packing => g.packingDegree ≠ 1
  | _ => True

private theorem prime_role_valid (g : Geometry) (role : Role) (h : role ∈ g.prime.roles .prime) :
    ValidRole g role := by
  have hf := frontend_valid g.prime .prime role h
  cases role with
  | sumcheck side stage round => rcases hf with ⟨rfl,hf⟩; exact hf
  | terminal side stage => rcases hf with ⟨rfl,hf⟩; exact hf
  | combine side stage entries => rcases hf with ⟨rfl,hf⟩; exact hf
  | packing => exact False.elim hf
  | _ => trivial

private theorem binary_role_valid (g : Geometry) (role : Role) (h : role ∈ g.binary.roles .binary) :
    ValidRole g role := by
  have hf := frontend_valid g.binary .binary role h
  cases role with
  | sumcheck side stage round => rcases hf with ⟨rfl,hf⟩; exact hf
  | terminal side stage => rcases hf with ⟨rfl,hf⟩; exact hf
  | combine side stage entries => rcases hf with ⟨rfl,hf⟩; exact hf
  | packing => exact False.elim hf
  | _ => trivial

/-- Every ordinary frontend message is indexed inside its actual public
stage, and packing occurs only when its degree is greater than one. -/
theorem role_valid (g : Geometry) (i : Fin g.roles.length) : ValidRole g (g.roles.get i) := by
  let role := g.roles.get i
  have h : role ∈ g.roles := List.get_mem g.roles i
  change ValidRole g role
  rw [g.roles_eq] at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
  rcases h with hfp | hp | hres | hconv | hb | hpack | hbatch | hopen
  · rw [hfp]; trivial
  · exact prime_role_valid g _ hp
  · rw [hres]; trivial
  · rw [hconv]; trivial
  · exact binary_role_valid g _ hb
  · by_cases he : g.packingDegree = 1
    · simp only [if_pos he,List.not_mem_nil] at hpack
    · have hr : role = .packing := by
        simpa only [if_neg he,List.mem_cons,List.not_mem_nil,or_false] using hpack
      rw [hr]
      exact he
  · rw [hbatch]; trivial
  · rw [hopen]; trivial

variable {g : Geometry} {fields : Fields} {Advice Auth : Type}
variable (shape : Shape g fields)

/-- The entry prefix has no prover-message placeholders. Fingerprint
responses and masked advice are taken from the body by `startFromBody`. -/
def StartMetadata : Start → Type
  | .none => Unit
  | .prime => CircuitStatement fields .prime shape.primePublic × CircuitSchedule 1
  | .binary => (CircuitStatement fields .binary shape.binaryPublic ×
      CircuitStatement fields .binary shape.binaryPublic) × CircuitSchedule 2

def startFromBody (body : Body g fields Advice Auth) :
    (start : Start) → StartMetadata shape start → StartData (Advice := Advice) shape start
  | .none, _ => ()
  | .prime, metadata => (body.fingerprints,metadata)
  | .binary, metadata => (body.advice,metadata)

/-- Only fixed source identifiers and layout are metadata. Polynomial
coefficients, mu, U/A and H/Z are deliberately absent from this type. -/
def RoleMetadata : Role → Type
  | .packing => PackingStatement shape
  | .batching => SourceStatement × SourceStatement
  | _ => Unit

private def packingValues (body : Body g fields Advice Auth) (h : g.packingDegree ≠ 1) :
    (Fin g.packingDegree → fields .binary) × fields .binary := by
  simpa only [PackingPayload,h,↓reduceIte] using body.packing

def roleFromBody (body : Body g fields Advice Auth) :
    (role : Role) → ValidRole g role → RoleMetadata shape role → RoleData shape role
  | .fingerprint, _, _ => ()
  | .inputAssertions .., _, _ => ⟨0,by decide⟩
  | .assertions _ stage .., _, _ => ⟨stage % 2^64,Nat.mod_lt _ (by decide)⟩
  | .sumcheck side stage round, valid, _ =>
      let hs := valid.choose
      ((body.frontend side) ⟨stage,hs⟩).coefficients ⟨round,valid.choose_spec⟩
  | .terminal side stage, valid, _ => ((body.frontend side) ⟨stage,valid⟩).cross
  | .combine side stage _, valid, _ => ((body.frontend side) ⟨stage,valid⟩).claims
  | .rowBatching, _, _ => ()
  | .rescaling, _, _ => ()
  | .conversion, _, _ => body.mu
  | .packing, valid, metadata => (metadata,(packingValues body valid).1)
  | .batching, _, metadata => (if h : g.packingDegree = 1 then
      (by simpa only [PackingA,h,↓reduceIte] using ()) else
      (by simpa only [PackingA,h,↓reduceIte] using (packingValues body h).2),metadata)
  | .opening, _, _ => (body.binaryBackend.response,body.primeBackend.response)

abbrev Metadata (i : Fin g.roles.length) := StartMetadata shape (startAt g i) × RoleMetadata shape (g.roles.get i)

/-- A complete packet receives every transmitted message from the body.
Only public or strictly-prefix-derived bind-only metadata is supplied. -/
def fromBody (i : Fin g.roles.length) (body : Body g fields Advice Auth) (metadata : Metadata shape i) :
    Data (Advice := Advice) shape i :=
  (startFromBody shape body (startAt g i) metadata.1,
    roleFromBody shape body (g.roles.get i) (role_valid g i) metadata.2)

private def roleBodyCache (body : Body g fields Advice Auth) (role : Role) : ProtocolWrites.Fresh g fields Advice where
  mu := if role = .conversion then some body.mu else none
  packingU := if role = .packing then (ProtocolWrites.packingPair body).map Prod.fst else none
  packingA := if role = .batching then (ProtocolWrites.packingPair body).map Prod.snd else none
  frontend := ProtocolWrites.frontendMessages body role
  responses := if role = .opening then some (body.binaryBackend.response,body.primeBackend.response) else none

private theorem roleFromBody_cache (body : Body g fields Advice Auth) (role : Role)
    (valid : ValidRole g role) (metadata : RoleMetadata shape role) :
    roleCache (Advice := Advice) shape role (roleFromBody shape body role valid metadata) = roleBodyCache body role := by
  cases role with
  | sumcheck side stage round =>
      simp only [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,dif_pos valid.choose,ProtocolWrites.layerMessage,dif_pos valid.choose_spec]
      rfl
  | terminal side stage =>
      have hs : stage < (g.frontend side).stages.length := valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,hs]
  | combine side stage entries =>
      have hs : stage < (g.frontend side).stages.length := valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,hs]
  | packing =>
      change g.packingDegree ≠ 1 at valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.packingPair,packingValues,valid]
  | batching =>
      have ha : (roleCache (Advice := Advice) shape .batching
          (roleFromBody shape body .batching valid metadata)).packingA =
          (ProtocolWrites.packingPair body).map Prod.snd := by
        change (if h : g.packingDegree = 1 then none else
          some (by simpa only [PackingA,h,↓reduceIte] using
            (roleFromBody shape body .batching valid metadata).1)) = _
        by_cases he : g.packingDegree = 1
        · simp [he,ProtocolWrites.packingPair]
        · simp [he,roleFromBody,ProtocolWrites.packingPair,packingValues]
      exact congrArg (fun value : Option (fields .binary) =>
        ({ packingA := value } : ProtocolWrites.Fresh g fields Advice)) ha
  | _ => rfl

private def startBodyCache (body : Body g fields Advice Auth) : Start → ProtocolWrites.Fresh g fields Advice
  | .none => {}
  | .prime => { fingerprints := some body.fingerprints }
  | .binary => { advice := some body.advice }

private theorem startFromBody_cache (body : Body g fields Advice Auth) (start : Start)
    (metadata : StartMetadata shape start) :
    startCache shape start (startFromBody shape body start metadata) = startBodyCache body start := by
  cases start <;> rfl

/-- Packet caches are derived from the actual body on every public index.
The caller supplies no equality between separate message descriptions. -/
theorem fromBody_cache (i : Fin g.roles.length) (body : Body g fields Advice Auth)
    (metadata : Metadata shape i) :
    cache shape i (fromBody shape i body metadata) = ProtocolWrites.fresh body i := by
  unfold cache fromBody
  rw [roleFromBody_cache,startFromBody_cache]
  have hne : g.primeStart ≠ g.binaryStart := by
    dsimp only [Geometry.binaryStart,Geometry.primeStart]
    omega
  by_cases hp : i.val = g.primeStart
  · simp [startAt,hp,startBodyCache,ProtocolWrites.fresh,roleBodyCache,hne]
  · by_cases hb : i.val = g.binaryStart
    · simp [startAt,hb,startBodyCache,ProtocolWrites.fresh,roleBodyCache,Ne.symm hne]
    · simp [startAt,hp,hb,startBodyCache,ProtocolWrites.fresh,roleBodyCache]

variable (repr : ProofBodyCodec.Representations fields Advice)

theorem parseCache_fromBody (i : Fin g.roles.length) (body : Body g fields Advice Auth)
    (metadata : Metadata shape i) :
    parseCache repr shape i ((codec repr shape i).encode (fromBody shape i body metadata)) =
      some (ProtocolWrites.fresh body i) := by
  rw [parseCache_encode,fromBody_cache]

end LfzkV2.Current.WireBlocks
