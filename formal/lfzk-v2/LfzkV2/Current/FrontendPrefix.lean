import LfzkV2.Current.FrontendTranscript
import LfzkV2.Current.ReplayBlocks
import LfzkV2.Current.BackendBody

/-! A frontend reader over actual chained query preimages.  A block contains
the bind-only writes and the frontend message; the latter is produced by the
message codec, never supplied as a correspondence proof.  Recovering an older
message traverses the query's recorded history and makes no oracle query.

`withFrontend` preserves the existing bind-only part of each block.  It fills
only the frontend window, so it introduces neither rounds nor changes to the
schedule.  The final byte encoder still has to frame these logical writes. -/
namespace LfzkV2.Current
open SumcheckV2
open Layered.Replay (Message Payload LayerRole layerMessage)

namespace Input
variable {roles : List Role} {Key Base Link Body E : Type}

def frontendWire (point : Input roles Key (Base × Message E) Link Body)
    (q : ℕ) : Message E :=
  (((point.atRank q).bind Input.block).map Prod.snd).getD .empty

end Input

namespace Replay.Encoding
variable {g : Geometry} {F : Fields} {Advice Authentication Key Base C E : Type}
variable [Field E] {out input : ℕ}
variable (e : Encoding g F Advice Authentication Key (Base × Message E) C)
  (circuit : Layered.Circuit E out input)
  (payloadOf : Output g F Advice Authentication → Payload circuit) (start : ℕ)

omit [Field E] in
private theorem frontendWire_of_block
    (code : Encoding g F Advice Authentication Key (Base × Message E) C)
    (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Key (Base × Message E) → Digest × C)
    (n q : ℕ) (hn : n ≤ g.roles.length) (hi : q < g.roles.length) (hbound : q ≤ n)
    (message : Message E)
    (hblock : ∀ past, (code.block proof ⟨q, hi⟩ past).2 = message) :
    ((code.chain initialLink).point proof H n).frontendWire q = message := by
  unfold Input.frontendWire
  rw [code.point_atRank initialLink proof H n q hn hbound]
  simp only [Option.bind_some]
  rw [code.point_block initialLink proof H ⟨q, hi⟩]
  simp only [Option.map_some, Option.getD_some]
  exact hblock _

def withFrontend : Encoding g F Advice Authentication Key (Base × Message E) C where
  context := e.context
  block proof i answers :=
    let earlier := e.block proof i answers
    if start ≤ i.val ∧ i.val < start+FrontendReplay.slots circuit then
      (earlier.1, FrontendTranscript.write circuit (payloadOf proof) (i.val-start))
    else earlier

omit [Field E] in
theorem withFrontend_wire (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Key (Base × Message E) → Digest × C)
    (n q : ℕ) (hn : n ≤ g.roles.length)
    (hq : q < FrontendReplay.slots circuit) (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (hbound : start+q ≤ n) :
    (((e.withFrontend circuit payloadOf start).chain initialLink).point proof H n).frontendWire
      (start+q) = FrontendTranscript.write circuit (payloadOf proof) q := by
  have hi : start+q < g.roles.length := by omega
  apply frontendWire_of_block (e.withFrontend circuit payloadOf start) initialLink proof H n
    (start+q) hn hi hbound _
  intro past
  have hw : start ≤ start+q ∧ start+q < start+FrontendReplay.slots circuit := by omega
  simp only [withFrontend, hw, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

/-- The payload seen at a boundary is reconstructed solely from the messages
already present in its chained preimage. Future zero defaults affect no role
whose message is already bound. -/
def frontendPayload (point : Point g F Advice Authentication Key (Base × Message E)) :
    Payload circuit :=
  FrontendTranscript.read circuit (fun q => point.frontendWire (start+q))

theorem withFrontend_message (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Key (Base × Message E) → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length)
    (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (role : LayerRole circuit) (hbound : start+FrontendReplay.queryIndex circuit role 0 ≤ n) :
    layerMessage circuit
      (frontendPayload circuit start
        (((e.withFrontend circuit payloadOf start).chain initialLink).point proof H n)) role =
      layerMessage circuit (payloadOf proof) role := by
  have hm := FrontendTranscript.layerMessage_readFrom_congr circuit role
    (fun q =>
      (((e.withFrontend circuit payloadOf start).chain initialLink).point proof H n).frontendWire
        (start+q))
    (FrontendTranscript.write circuit (payloadOf proof)) 0
    (e.withFrontend_wire circuit payloadOf start initialLink proof H n
      (FrontendReplay.queryIndex circuit role 0) hn
      (by simpa only [Nat.zero_add] using FrontendReplay.queryIndex_lt circuit role 0) hfit hbound)
  change layerMessage circuit (frontendPayload circuit start _) role =
    layerMessage circuit (FrontendTranscript.read circuit
      (FrontendTranscript.write circuit (payloadOf proof))) role at hm
  simpa only [FrontendTranscript.read_write] using hm

omit [Field E] in
/-- The later backend opening encoder preserves all earlier frontend
messages. Disjointness is just a public inequality between schedule positions;
it is not a proof-dependent correspondence premise. -/
theorem withOpening_frontendWire {Response : Type}
    (responses : Output g F Advice Authentication → Response)
    (encode : Response → Base × Message E)
    (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Key (Base × Message E) → Digest × C)
    (n q : ℕ) (hn : n ≤ g.roles.length) (hq : q < FrontendReplay.slots circuit)
    (hbefore : start+FrontendReplay.slots circuit ≤ g.openingIndex.val)
    (hbound : start+q ≤ n) :
    ((((e.withFrontend circuit payloadOf start).withOpening responses encode).chain initialLink).point
      proof H n).frontendWire (start+q) = FrontendTranscript.write circuit (payloadOf proof) q := by
  have hi : start+q < g.roles.length := lt_of_lt_of_le (by omega) (Nat.le_of_lt g.openingIndex.isLt)
  apply frontendWire_of_block ((e.withFrontend circuit payloadOf start).withOpening responses encode)
    initialLink proof H n (start+q) hn hi hbound _
  intro past
  have hne : (⟨start+q, hi⟩ : Fin g.roles.length) ≠ g.openingIndex := by
    intro heq
    have hv := congrArg Fin.val heq
    change start+q = g.openingIndex.val at hv
    omega
  rw [withOpening_block_earlier _ responses encode proof _ past hne]
  have hw : start ≤ start+q ∧ start+q < start+FrontendReplay.slots circuit := by omega
  simp only [withFrontend, hw, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem withOpening_frontendMessage {Response : Type}
    (responses : Output g F Advice Authentication → Response)
    (encode : Response → Base × Message E)
    (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Key (Base × Message E) → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length)
    (hbefore : start+FrontendReplay.slots circuit ≤ g.openingIndex.val)
    (role : LayerRole circuit) (hbound : start+FrontendReplay.queryIndex circuit role 0 ≤ n) :
    layerMessage circuit
      (frontendPayload circuit start
        ((((e.withFrontend circuit payloadOf start).withOpening responses encode).chain initialLink).point
          proof H n)) role = layerMessage circuit (payloadOf proof) role := by
  have hm := FrontendTranscript.layerMessage_readFrom_congr circuit role
    (fun q =>
      ((((e.withFrontend circuit payloadOf start).withOpening responses encode).chain initialLink).point
        proof H n).frontendWire (start+q))
    (FrontendTranscript.write circuit (payloadOf proof)) 0
    (e.withOpening_frontendWire circuit payloadOf start responses encode initialLink proof H n
      (FrontendReplay.queryIndex circuit role 0) hn
      (by simpa only [Nat.zero_add] using FrontendReplay.queryIndex_lt circuit role 0) hbefore hbound)
  change layerMessage circuit (frontendPayload circuit start _) role =
    layerMessage circuit (FrontendTranscript.read circuit
      (FrontendTranscript.write circuit (payloadOf proof))) role at hm
  simpa only [FrontendTranscript.read_write] using hm

end Replay.Encoding
end LfzkV2.Current
