import LfzkV2.Current.Format
import LfzkV2.Current.ZeroKnowledge.CompleteTerminalBody
import LfzkV2.Current.ReplayCongruence

/-! Terminal filling preserves every canonical prefix through the opening boundary.
Both backend arrays and terminal authentication are absent from every
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

variable  {publicCount : ℕ} (fmt : Format g fields Advice publicCount)
variable (binaryRequest : (Fin publicCount → Bool) → Fin fmt.binaryPublic → fields .binary)
variable (metadata : fmt.RequestMetadata C)
variable (request : fmt.Request)
local notation "Output" => Replay.Output g fields Advice (OpeningBody.Authentication g)
local notation "Point" => fmt.Point
local notation "e" => fmt.encoding binaryRequest metadata request

def proof (pending : Output) (terminal : Body g fields Advice (OpeningBody.Authentication g)) : Output :=
  { pending with body := fill pending.body terminal }

theorem block_before (pending : Output) (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) (past : Fin i.val → C) :
    (e).block (proof pending terminal) i past = (e).block pending i past := by
  apply fmt.block_writes_congr binaryRequest metadata request (proof pending terminal) pending i past rfl
  funext j
  apply fresh_before
  change j.val < g.openingIndex.val
  have := j.isLt
  omega

theorem replay_before (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).replay (proof pending terminal) H index =
      ((e).chain initial).replay pending H index :=
  Replay.Encoding.replay_eq_of_blocks e initial (proof pending terminal) pending H index
    (lt_trans before g.openingIndex.isLt) rfl
    (fun i bound past => block_before fmt binaryRequest metadata request
      pending terminal i (by omega) past)

theorem point_before (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (H : Point → Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    ((e).chain initial).point (proof pending terminal) H index =
      ((e).chain initial).point pending H index :=
  congrArg ((e).chain initial).input
    (replay_before fmt binaryRequest metadata request initial pending terminal H index before)

/-- Opened rows and authentication appear only in the final complete body.
Once the two response arrays are fixed, filling those values preserves
every ordinary challenge input, including the opening challenge. -/
theorem block_same_responses (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (i : Fin g.roles.length) (past : Fin i.val → C) :
    (e).block (proof pending terminal) i past = (e).block pending i past := by
  apply fmt.block_writes_congr binaryRequest metadata request (proof pending terminal) pending i past rfl
  funext j
  simp only [Format.writes,ProtocolWrites.fresh,proof,fill,ProtocolWrites.packingPair,
    ProtocolWrites.frontendMessages,Body.frontend,binary,prime]

theorem point_same_responses (initial : Digest) (pending : Output)
    (terminal : Body g fields Advice (OpeningBody.Authentication g))
    (binary : terminal.binaryBackend.response = pending.body.binaryBackend.response)
    (prime : terminal.primeBackend.response = pending.body.primeBackend.response)
    (H : Point → Digest × C) (index : ℕ) (inside : index < g.roles.length) :
    ((e).chain initial).point (proof pending terminal) H index =
      ((e).chain initial).point pending H index := by
  apply congrArg ((e).chain initial).input
  apply Replay.Encoding.replay_eq_of_blocks e initial (proof pending terminal) pending H index inside rfl
  intro i _ past
  exact block_same_responses fmt binaryRequest metadata request
    pending terminal binary prime i past

end LfzkV2.Current.ZeroKnowledge.CompleteTerminal
