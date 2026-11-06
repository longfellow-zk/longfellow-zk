import LfzkV2.Current.FrontendSchedule
import LfzkV2.Current.ReplayBlocks
import LfzkV2.Current.Finite

/-! Fresh prover writes in the concrete mdoc schedule. These are logical
views of existing writes, not new serialized tags or additional rounds.
`none` means no write, and an empty frontend message has no field bytes.
Public/derived bind-only metadata is kept in the separate block component.

Every value below comes from the actual typed proof body. Reading an earlier
write traverses the recorded query history; it neither consults future proof
fields nor asks the oracle. Canonical byte framing remains a separate layer. -/
namespace LfzkV2.Current
open SumcheckV2
open Layered.Replay (Message)

def Geometry.frontend (g : Geometry) : Side → Frontend
  | .binary => g.binary
  | .prime => g.prime

def Body.frontend {g : Geometry} {F : Fields} {Advice Auth : Type}
    (body : Body g F Advice Auth) : (side : Side) → FrontendPayload (F side) (g.frontend side)
  | .binary => body.binary
  | .prime => body.prime

namespace ProtocolWrites
variable {g : Geometry} {F : Fields} {Advice Auth : Type}

inductive Kind where
  | round (index : ℕ)
  | cross
  | claims

def layerMessage {E : Type} {rounds : ℕ} (payload : LayerPayload E rounds) : Kind → Message E
  | .round i => if h : i < rounds then
      let p := payload.coefficients ⟨i,h⟩
      .round ⟨p.1,p.2⟩
    else .empty
  | .cross => .cross payload.cross
  | .claims => .claims payload.claims.1 payload.claims.2

def stageMessage {E : Type} {frontend : Frontend}
    (payload : FrontendPayload E frontend) (stage : ℕ) (kind : Kind) : Message E :=
  if h : stage < frontend.stages.length then layerMessage (payload ⟨stage,h⟩) kind else .empty

/-- Exactly one field can write a frontend message in a boundary. Assertion
and entry roles write no polynomial; they only consume challenge coordinates. -/
def frontendMessages (body : Body g F Advice Auth) : Role → (side : Side) → Message (F side)
  | .sumcheck side stage round =>
      Function.update (fun _ => .empty) side (stageMessage (body.frontend side) stage (.round round))
  | .terminal side stage =>
      Function.update (fun _ => .empty) side (stageMessage (body.frontend side) stage .cross)
  | .combine side stage _ =>
      Function.update (fun _ => .empty) side (stageMessage (body.frontend side) stage .claims)
  | _ => fun _ => .empty

def packingPair (body : Body g F Advice Auth) : Option ((Fin g.packingDegree → F .binary) × F .binary) :=
  if h : g.packingDegree = 1 then none else
    some (by simpa only [PackingPayload, h, ↓reduceIte] using body.packing)

structure Fresh (g : Geometry) (F : Fields) (Advice : Type) where
  fingerprints : Option (Fingerprints F) := none
  mu : Option (F .prime) := none
  advice : Option Advice := none
  packingU : Option (Fin g.packingDegree → F .binary) := none
  packingA : Option (F .binary) := none
  frontend : (side : Side) → Message (F side) := fun _ => .empty
  responses : Option (Response g (F .binary) × Response g (F .prime)) := none

/-- Bind-only messages are assigned to the next actual boundary. In
particular fingerprints precede prime sumcheck, and masked advice precedes
binary sumcheck. The two conversion challenges share the one conversion role. -/
def fresh (body : Body g F Advice Auth) (i : Fin g.roles.length) : Fresh g F Advice where
  fingerprints := if i.val = g.primeStart then some body.fingerprints else none
  mu := if g.roles.get i = .conversion then some body.mu else none
  advice := if i.val = g.binaryStart then some body.advice else none
  packingU := if g.roles.get i = .packing then (packingPair body).map Prod.fst else none
  packingA := if g.roles.get i = .batching then (packingPair body).map Prod.snd else none
  frontend := frontendMessages body (g.roles.get i)
  responses := if g.roles.get i = .opening then
    some (body.binaryBackend.response,body.primeBackend.response) else none

noncomputable instance freshFintype [∀ side, Fintype (F side)] [Fintype Advice] : Fintype (Fresh g F Advice) := by
  classical
  apply Fintype.ofInjective (fun writes : Fresh g F Advice =>
    (writes.fingerprints,writes.mu,writes.advice,writes.packingU,writes.packingA,
      writes.frontend .binary,writes.frontend .prime,writes.responses))
  intro a b h
  have hm : a.frontend = b.frontend := by
    funext side
    cases side
    · exact congrArg (fun x => x.2.2.2.2.2.1) h
    · exact congrArg (fun x => x.2.2.2.2.2.2.1) h
  cases a
  cases b
  dsimp only at hm h
  cases hm
  cases h
  rfl

end ProtocolWrites

namespace Input
variable {roles : List Role} {Key Block Link Body X : Type}

def readAt (point : Input roles Key Block Link Body) (q : ℕ) (read : Block → Option X) : Option X :=
  ((point.atRank q).bind Input.block).bind read

end Input

namespace Replay.Encoding
variable {g : Geometry} {F : Fields} {Advice Auth Key Block C X : Type}
variable (e : Encoding g F Advice Auth Key Block C)

/-- This equality holds before any verifier acceptance assumption. It fixes
the complete written block using strict earlier answers, so a later parser
cannot substitute an unrelated message for the one actually hashed. -/
theorem readAt_replay (initialLink : Digest) (proof : Output g F Advice Auth)
    (H : Point g F Advice Auth Key Block → Digest × C) (n : ℕ) (hn : n ≤ g.roles.length)
    (i : Fin g.roles.length) (hi : i.val ≤ n) (read : Block → Option X) :
    ((e.chain initialLink).point proof H n).readAt i.val read =
      read (e.block proof i (fun j => (H ((e.chain initialLink).point proof H j.val)).2)) := by
  unfold Input.readAt
  rw [e.point_atRank initialLink proof H n i.val hn hi]
  simp only [Option.bind_some]
  rw [e.point_block initialLink proof H i]
  rfl

variable {Base : Type}
variable (earlier : Encoding g F Advice Auth Key (Base × ProtocolWrites.Fresh g F Advice) C)

/-- Fill the prover-write component from the actual body. Bind-only public
metadata retains its earlier encoder; it must be instantiated by public setup. -/
def withProtocolWrites : Encoding g F Advice Auth Key (Base × ProtocolWrites.Fresh g F Advice) C where
  context := earlier.context
  block proof i past := ((earlier.block proof i past).1, ProtocolWrites.fresh proof.body i)

theorem protocol_readAt (initialLink : Digest) (proof : Output g F Advice Auth)
    (H : Point g F Advice Auth Key (Base × ProtocolWrites.Fresh g F Advice) → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) (i : Fin g.roles.length) (hi : i.val ≤ n)
    (read : ProtocolWrites.Fresh g F Advice → Option X) :
    (((earlier.withProtocolWrites).chain initialLink).point proof H n).readAt i.val (read ∘ Prod.snd) =
      read (ProtocolWrites.fresh proof.body i) := by
  rw [(earlier.withProtocolWrites).readAt_replay initialLink proof H n hn i hi]
  rfl

end Replay.Encoding
end LfzkV2.Current
