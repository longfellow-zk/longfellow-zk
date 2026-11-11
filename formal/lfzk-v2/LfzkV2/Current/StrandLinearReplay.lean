import LfzkV2.Current.StrandRuntime
import LfzkV2.Current.Replay
import TranscriptV2.StrandLinear

/-! The runtime's canonical packets instantiate numbered linear replay.
This bridge compares only transcript history. Challenge caches are used by
the arithmetic verifier but do not change the absorbed packet at a boundary. -/
namespace LfzkV2.Current.StrandLinearReplay
open CanonicalPrefix QueryRuntime TranscriptV2

section Packet
variable {roles : List Role} {Terminal Key Fresh : Type} {capacity : ℕ}
variable (bodyCodec : PrefixCodec Terminal)

def packet (point : Input roles Key (Block capacity Fresh) Digest Terminal) : Bytes :=
  match point with
  | .round i _ current => current.1.bytes ++ StrandQueryCodec.roundFooter (roles.get i).domain
  | .finalSeal _ body => StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode body)

def payload : Strand.History → Bytes
  | .root message => message
  | .child _ _ message => message

theorem history_payload (point : Input roles Key (Block capacity Fresh) Digest Terminal) :
    payload (StrandRuntime.history bodyCodec point) = packet bodyCodec point := by
  cases point with
  | round i previous current =>
      rcases i with ⟨n,within⟩
      cases n <;> rfl
  | finalSeal previous body =>
      cases roles <;> rfl

end Packet

variable {g : Geometry} {fields : Fields} {Advice Auth Key Fresh C : Type}
variable {capacity blocks : ℕ}
variable (bodyCodec : PrefixCodec (Body g fields Advice Auth))

variable (encoding : Replay.Encoding g fields Advice Auth Key (Block capacity Fresh) C)
variable (fallback : C) (proof : Replay.Output g fields Advice Auth)

/-- Freeze the actual ordinary packets and the canonical terminal body. -/
def packets (index : ℕ) : Bytes :=
  if within : index < g.roles.length then
    (encoding.block proof ⟨index,within⟩ (fun _ => fallback)).1.bytes ++
      StrandQueryCodec.roundFooter (g.roles.get ⟨index,within⟩).domain
  else StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode proof.body)

variable (independent : ∀ i first second, encoding.block proof i first = encoding.block proof i second)

include independent in
theorem stateAt_packet (n : ℕ) (within : n ≤ g.roles.length)
    (previous : History Key (Block capacity Fresh) Digest n) (answers : Fin n → C) :
    packet bodyCodec (encoding.stateAt proof n within previous answers).point =
      packets bodyCodec encoding fallback proof n := by
  by_cases earlier : n < g.roles.length
  · simp only [Replay.Encoding.stateAt,packets,dif_pos earlier,packet]
    rw [independent ⟨n,earlier⟩ answers (fun _ => fallback)]
  · have last : n = g.roles.length := by omega
    subst n
    simp only [Replay.Encoding.stateAt,packets,dif_neg earlier,packet]

variable (initial : Digest)
variable (sample : Replay.Point g fields Advice Auth Key (Block capacity Fresh) →
  Merkle.RandomOracle.Tree Strand.Word Digest (Option C) blocks)
local notation "oracle" => TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback

include independent in
theorem point_packet (H : Strand.Oracle) (n : ℕ) (within : n ≤ g.roles.length) :
    packet bodyCodec ((encoding.chain initial).point proof (oracle H) n) =
      packets bodyCodec encoding fallback proof n := by
  cases n with
  | zero => exact stateAt_packet bodyCodec encoding fallback proof independent _ _ _ _
  | succ n =>
      have earlier : n < g.roles.length := by omega
      have rank := (encoding.chain initial).point_rank proof (oracle H) (by omega : n ≤ g.roles.length)
      simp only [Chain.point,Chain.replay,dif_pos earlier]
      change packet bodyCodec (encoding.advance proof
        ((encoding.chain initial).replay proof (oracle H) n)
        ((oracle H) ((encoding.chain initial).point proof (oracle H) n))).point = _
      generalize state : (encoding.chain initial).replay proof (oracle H) n = current
      change ((encoding.chain initial).replay proof (oracle H) n).point.rank = n at rank
      rw [state] at rank
      rcases current with ⟨point,answers⟩
      cases point with
      | round i previous block =>
          change i.val = n at rank
          rw [Replay.Encoding.advance,stateAt_packet bodyCodec encoding fallback proof independent,rank]
      | finalSeal previous body =>
          change g.roles.length = n at rank
          omega

include independent in
/-- Exact agreement with the fixed-packet chain used by missing-query
charging. This discharges the replay abstraction without any certificate
about the execution supplied by a caller. -/
theorem history_replay (H : Strand.Oracle) (n : ℕ) (within : n ≤ g.roles.length) :
    StrandRuntime.history bodyCodec ((encoding.chain initial).point proof (oracle H) n) =
      StrandLinear.replay (packets bodyCodec encoding fallback proof) H n := by
  induction n with
  | zero =>
      have rank := (encoding.chain initial).point_rank proof (oracle H) (Nat.zero_le _)
      change ((encoding.chain initial).point proof (oracle H) 0).rank = 0 at rank
      obtain ⟨message,current⟩ := StrandRuntime.history_root bodyCodec
        ((encoding.chain initial).point proof (oracle H) 0) rank
      have messageEq := history_payload bodyCodec ((encoding.chain initial).point proof (oracle H) 0)
      rw [current,point_packet bodyCodec encoding fallback proof independent initial sample H 0 within] at messageEq
      change message = packets bodyCodec encoding fallback proof 0 at messageEq
      rw [current,messageEq]
      rfl
  | succ n ih =>
      have earlier : n < g.roles.length := by omega
      have parent := (encoding.chain initial).point_parent proof (oracle H) earlier
      obtain ⟨message,current⟩ := StrandRuntime.history_parent bodyCodec initial _ _ parent
      have link := (encoding.chain initial).point_link proof (oracle H) earlier
      change Input.claimed initial ((encoding.chain initial).point proof (oracle H) (n+1)) =
        (oracle H ((encoding.chain initial).point proof (oracle H) n)).1 at link
      rw [TranscriptV2.StrandVerifier.oracle_node] at link
      have messageEq := history_payload bodyCodec ((encoding.chain initial).point proof (oracle H) (n+1))
      rw [current,point_packet bodyCodec encoding fallback proof independent initial sample H (n+1) within] at messageEq
      change message = packets bodyCodec encoding fallback proof (n+1) at messageEq
      rw [current,link,messageEq,ih (by omega)]
      rfl

end LfzkV2.Current.StrandLinearReplay
