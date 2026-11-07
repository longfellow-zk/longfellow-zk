import LfzkV2.Current.ZeroKnowledge.CompleteTerminal

/-! Opened rows and authentication enter the final seal. The opening query
itself depends on the two H/Z responses, so filling the rows and authentication
while preserving those responses leaves that query unchanged. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteTerminalOpening
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C : Type}

theorem fresh_eq (body terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = body.binaryBackend.response)
    (prime : terminal.primeBackend.response = body.primeBackend.response) (i : Fin g.roles.length) :
    ProtocolWrites.fresh (CompleteTerminal.fill body terminal) i = ProtocolWrites.fresh body i := by
  simp only [ProtocolWrites.fresh,CompleteTerminal.fill,ProtocolWrites.packingPair,
    ProtocolWrites.frontendMessages,Body.frontend,binary,prime]

variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "e" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
private theorem role_eq (body terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = body.binaryBackend.response)
    (prime : terminal.primeBackend.response = body.primeBackend.response)
    (role : Role) (valid : WireBlocks.ValidRole g role) (roleMeta : WireBlocks.RoleMetadata shape role) :
    WireBlocks.roleFromBody shape (CompleteTerminal.fill body terminal) role valid roleMeta =
      WireBlocks.roleFromBody shape body role valid roleMeta := by
  cases role <;> try rfl
  exact Prod.ext binary prime

theorem block_eq (pending : Output) (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (i : Fin g.roles.length) (past : Fin i.val → C) :
    (e).block (CompleteTerminal.proof pending terminal) i past = (e).block pending i past := by
  have writes : CanonicalRequest.writes (CompleteTerminal.fill pending.body terminal) i = CanonicalRequest.writes pending.body i := by
    funext j
    exact fresh_eq pending.body terminal binary prime _
  dsimp only [CanonicalRequest.encoding,CanonicalRequest.block,CompleteTerminal.proof]
  split_ifs with zero
  · rfl
  · unfold CanonicalRequest.ordinaryData
    change (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
      (WireBlocks.fromRequest shape _ _ i (CompleteTerminal.fill pending.body terminal)
        (metadata request i (CanonicalRequest.writes (CompleteTerminal.fill pending.body terminal) i) past)) = _
    rw [writes]
    unfold WireBlocks.fromRequest WireBlocks.fromBody
    congr 2
    exact role_eq shape pending.body terminal binary prime (g.roles.get i) _ _

theorem replay_eq (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) (index : ℕ) (inside : index < g.roles.length) :
    ((e).chain initial).replay (CompleteTerminal.proof pending terminal) H index =
      ((e).chain initial).replay pending H index :=
  Replay.Encoding.replay_eq_of_blocks e initial (CompleteTerminal.proof pending terminal) pending H index inside rfl
    (fun i _ past => block_eq repr shape setup publicCount binaryRequest metadata request
      pending terminal binary prime i past)

theorem point_eq (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) (index : ℕ) (inside : index < g.roles.length) :
    ((e).chain initial).point (CompleteTerminal.proof pending terminal) H index =
      ((e).chain initial).point pending H index :=
  congrArg ((e).chain initial).input (replay_eq repr shape setup publicCount binaryRequest metadata request
    initial pending terminal binary prime H index inside)

theorem opening_point (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) :
    ((e).chain initial).point (CompleteTerminal.proof pending terminal) H g.openingIndex.val =
      ((e).chain initial).point pending H g.openingIndex.val :=
  point_eq repr shape setup publicCount binaryRequest metadata request initial pending terminal binary prime H
    g.openingIndex.val g.openingIndex.isLt

theorem opening_point_zero (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) :
    ((e).chain initial).point (⟨CompleteTerminal.fill pending.body terminal,fun _ => 0⟩ : Output) H g.openingIndex.val =
      ((e).chain initial).point pending H g.openingIndex.val := by
  have same := OracleRuntime.point_same_body repr shape setup publicCount binaryRequest metadata request initial
    (⟨CompleteTerminal.fill pending.body terminal,fun _ => 0⟩ : Output)
    (CompleteTerminal.proof pending terminal) rfl H g.openingIndex.val
  exact same.trans (opening_point repr shape setup publicCount binaryRequest metadata request initial pending terminal binary prime H)

theorem programAndFinalize_update (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) (answer : Digest × C) :
    let full := CompleteTerminal.fill pending.body terminal
    let oracle := Function.update H (((e).chain initial).point pending H g.openingIndex.val) answer
    OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request initial full H answer =
      (OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial full oracle,oracle) := by
  exact congrArg (fun point : Point =>
    (OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial
      (CompleteTerminal.fill pending.body terminal) (Function.update H point answer),Function.update H point answer))
    (opening_point_zero repr shape setup publicCount binaryRequest metadata request initial pending terminal binary prime H)

end LfzkV2.Current.ZeroKnowledge.CompleteTerminalOpening
