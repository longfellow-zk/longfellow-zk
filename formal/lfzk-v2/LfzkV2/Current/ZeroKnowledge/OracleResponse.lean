import LfzkV2.Current.ZeroKnowledge.OracleRuntime

/-! Backend responses are written only at the last ordinary boundary.
Filling those arrays after sampling the batching coin cannot change the
batching preimage or any earlier canonical prefix. This is derived from the
actual packet constructors, including metadata's prefix-only interface. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleResponse
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C : Type}

def fillBoth (body : Body g fields Advice (OpeningBody.Authentication g))
    (response : Response g (fields .binary) × Response g (fields .prime)) : Body g fields Advice (OpeningBody.Authentication g) :=
  { body with
    binaryBackend := { body.binaryBackend with response := response.1 }
    primeBackend := { body.primeBackend with response := response.2 } }

theorem freshBoth_before (body : Body g fields Advice (OpeningBody.Authentication g))
    (response : Response g (fields .binary) × Response g (fields .prime)) (i : Fin g.roles.length)
    (before : i.val < g.openingIndex.val) :
    ProtocolWrites.fresh (fillBoth body response) i = ProtocolWrites.fresh body i := by
  have notOpening : g.roles.get i ≠ .opening := by
    intro h
    have same := (g.get_eq_opening_iff i).mp h
    subst i
    exact Nat.lt_irrefl _ before
  simp only [ProtocolWrites.fresh,notOpening,if_false,fillBoth,ProtocolWrites.packingPair,
    ProtocolWrites.frontendMessages,Body.frontend]

variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)

local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "e" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request

def proofBoth (pending : Output) (response : Response g (fields .binary) × Response g (fields .prime)) : Output :=
  { pending with body := fillBoth pending.body response }

private theorem role_before (body : Body g fields Advice (OpeningBody.Authentication g))
    (response : Response g (fields .binary) × Response g (fields .prime)) (role : Role) (valid : WireBlocks.ValidRole g role)
    (metadata : WireBlocks.RoleMetadata shape role) (notOpening : role ≠ .opening) :
    WireBlocks.roleFromBody shape (fillBoth body response) role valid metadata =
      WireBlocks.roleFromBody shape body role valid metadata := by
  cases role <;> try rfl
  exact (notOpening rfl).elim

theorem blockBoth_before (pending : Output) (response : Response g (fields .binary) × Response g (fields .prime))
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) (past : Fin i.val → C) :
    (e).block (proofBoth pending response) i past = (e).block pending i past := by
  have writes : CanonicalRequest.writes (fillBoth pending.body response) i =
      CanonicalRequest.writes pending.body i := by
    funext j
    apply freshBoth_before
    change j.val < g.openingIndex.val
    have hj := j.isLt
    omega
  have notOpening : g.roles.get i ≠ .opening := by
    intro h
    have same := (g.get_eq_opening_iff i).mp h
    subst i
    exact Nat.lt_irrefl _ before
  dsimp only [CanonicalRequest.encoding,CanonicalRequest.block,proofBoth]
  split_ifs with zero
  · rfl
  · unfold CanonicalRequest.ordinaryData
    change (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
        (WireBlocks.fromRequest shape _ _ i (fillBoth pending.body response)
          (metadata request i (CanonicalRequest.writes (fillBoth pending.body response) i) past)) = _
    rw [writes]
    unfold WireBlocks.fromRequest WireBlocks.fromBody
    congr 2
    exact role_before shape pending.body response (g.roles.get i) _ _ notOpening

private theorem stateAtBoth_before (pending : Output) (response : Response g (fields .binary) × Response g (fields .prime))
    (index : ℕ) (before : index < g.openingIndex.val)
    (history : History (CanonicalRequest.Key publicCount)
      (QueryRuntime.Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
        (CanonicalRequest.Fresh (g := g) (fields := fields) (Advice := Advice))) Digest index)
    (answers : Fin index → C) :
    (e).stateAt (proofBoth pending response) index (by have := g.openingIndex.isLt; omega) history answers =
      (e).stateAt pending index (by have := g.openingIndex.isLt; omega) history answers := by
  have inside : index < g.roles.length := lt_trans before g.openingIndex.isLt
  simp only [Replay.Encoding.stateAt,dif_pos inside]
  rw [blockBoth_before repr shape setup publicCount binaryRequest metadata request pending response _ before]

/-- The entire state, including every earlier challenge, is unchanged. -/
theorem replayBoth_before (initial : Digest) (pending : Output) (response : Response g (fields .binary) × Response g (fields .prime))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).replay (proofBoth pending response) H index =
      ((e).chain initial).replay pending H index := by
  induction index with
  | zero =>
      exact stateAtBoth_before repr shape setup publicCount binaryRequest metadata request pending response
        0 before _ _
  | succ index ih =>
      have earlier : index < g.openingIndex.val := by omega
      have inside : index < g.roles.length := lt_trans earlier g.openingIndex.isLt
      simp only [TranscriptV2.Chain.replay,dif_pos inside]
      rw [ih earlier]
      have rank := ((e).chain initial).point_rank pending H (Nat.le_of_lt inside)
      change Input.rank (((e).chain initial).replay pending H index).point = index at rank
      generalize hs : ((e).chain initial).replay pending H index = state
      rw [hs] at rank
      rcases state with ⟨point,answers⟩
      cases point with
      | round i history block =>
          change i.val = index at rank
          exact stateAtBoth_before repr shape setup publicCount binaryRequest metadata request pending response
            (i.val+1) (by omega) _ _
      | finalSeal history body =>
          change g.roles.length = index at rank
          omega

theorem batchingBoth_point (initial : Digest) (pending : Output) (response : Response g (fields .binary) × Response g (fields .prime))
    (H : Point → Digest × C) :
    ((e).chain initial).point (proofBoth pending response) H g.batchingIndex.val =
      ((e).chain initial).point pending H g.batchingIndex.val :=
  congrArg ((e).chain initial).input
    (replayBoth_before repr shape setup publicCount binaryRequest metadata request initial pending response H
      g.batchingIndex.val (by have := g.openingIndex_val; omega))


/-- The binary-only form is retained for primary-mask counting. The joint
runtime uses `fillBoth`; both share the same prefix-invariance proof. -/
def fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (response : Response g (fields .binary)) : Body g fields Advice (OpeningBody.Authentication g) :=
  fillBoth body (response,body.primeBackend.response)

def proof (pending : Output) (response : Response g (fields .binary)) : Output :=
  proofBoth pending (response,pending.body.primeBackend.response)

theorem fresh_before (body : Body g fields Advice (OpeningBody.Authentication g))
    (response : Response g (fields .binary)) (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) :
    ProtocolWrites.fresh (fill body response) i = ProtocolWrites.fresh body i :=
  freshBoth_before body (response,body.primeBackend.response) i before

theorem block_before (pending : Output) (response : Response g (fields .binary))
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) (past : Fin i.val → C) :
    (e).block (proof pending response) i past = (e).block pending i past :=
  blockBoth_before repr shape setup publicCount binaryRequest metadata request pending
    (response,pending.body.primeBackend.response) i before past

theorem replay_before (initial : Digest) (pending : Output) (response : Response g (fields .binary))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).replay (proof pending response) H index =
      ((e).chain initial).replay pending H index :=
  replayBoth_before repr shape setup publicCount binaryRequest metadata request initial pending
    (response,pending.body.primeBackend.response) H index before

theorem batching_point (initial : Digest) (pending : Output) (response : Response g (fields .binary))
    (H : Point → Digest × C) :
    ((e).chain initial).point (proof pending response) H g.batchingIndex.val =
      ((e).chain initial).point pending H g.batchingIndex.val :=
  batchingBoth_point repr shape setup publicCount binaryRequest metadata request initial pending
    (response,pending.body.primeBackend.response) H

end LfzkV2.Current.ZeroKnowledge.OracleResponse
