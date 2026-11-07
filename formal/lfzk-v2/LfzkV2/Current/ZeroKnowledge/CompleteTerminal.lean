import LfzkV2.Current.ZeroKnowledge.OracleRuntime
import LfzkV2.Current.ZeroKnowledge.CompleteTerminalBody
import LfzkV2.Current.ReplayCongruence

/-! Both backend arrays and terminal authentication are absent from every
earlier canonical packet. Filling those fields after the batching query
preserves its exact input and all strict earlier answers. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteTerminal
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C : Type}

theorem fresh_before (body terminal : Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) :
    ProtocolWrites.fresh (fill body terminal) i = ProtocolWrites.fresh body i := by
  have notOpening : g.roles.get i ≠ .opening := by
    intro equal
    have same := (g.get_eq_opening_iff i).mp equal
    subst i
    exact Nat.lt_irrefl _ before
  simp only [ProtocolWrites.fresh,notOpening,if_false,fill,ProtocolWrites.packingPair,
    ProtocolWrites.frontendMessages,Body.frontend]

variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "e" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request

def proof (pending : Output) (terminal : Body g fields Advice (OpeningBody.Authentication g)) : Output :=
  { pending with body := fill pending.body terminal }

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
private theorem role_before (body terminal : Body g fields Advice (OpeningBody.Authentication g))
    (role : Role) (valid : WireBlocks.ValidRole g role)
    (metadata : WireBlocks.RoleMetadata shape role) (notOpening : role ≠ .opening) :
    WireBlocks.roleFromBody shape (fill body terminal) role valid metadata =
      WireBlocks.roleFromBody shape body role valid metadata := by
  cases role <;> try rfl
  exact (notOpening rfl).elim

theorem block_before (pending : Output) (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) (past : Fin i.val → C) :
    (e).block (proof pending terminal) i past = (e).block pending i past := by
  have writes : CanonicalRequest.writes (fill pending.body terminal) i =
      CanonicalRequest.writes pending.body i := by
    funext j
    apply fresh_before
    change j.val < g.openingIndex.val
    have := j.isLt
    omega
  have notOpening : g.roles.get i ≠ .opening := by
    intro equal
    have same := (g.get_eq_opening_iff i).mp equal
    subst i
    exact Nat.lt_irrefl _ before
  dsimp only [CanonicalRequest.encoding,CanonicalRequest.block,proof]
  split_ifs with zero
  · rfl
  · unfold CanonicalRequest.ordinaryData
    change (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
        (WireBlocks.fromRequest shape _ _ i (fill pending.body terminal)
          (metadata request i (CanonicalRequest.writes (fill pending.body terminal) i) past)) = _
    rw [writes]
    unfold WireBlocks.fromRequest WireBlocks.fromBody
    congr 2
    exact role_before shape pending.body terminal (g.roles.get i) _ _ notOpening

theorem replay_before (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).replay (proof pending terminal) H index =
      ((e).chain initial).replay pending H index :=
  Replay.Encoding.replay_eq_of_blocks e initial (proof pending terminal) pending H index
    (lt_trans before g.openingIndex.isLt) rfl
    (fun i bound past => block_before repr shape setup publicCount binaryRequest metadata request
      pending terminal i (by omega) past)

theorem point_before (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).point (proof pending terminal) H index =
      ((e).chain initial).point pending H index :=
  congrArg ((e).chain initial).input
    (replay_before repr shape setup publicCount binaryRequest metadata request initial pending terminal H index before)

end LfzkV2.Current.ZeroKnowledge.CompleteTerminal
