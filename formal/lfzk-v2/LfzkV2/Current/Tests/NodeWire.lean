import LfzkV2.Current.StrandLinearReplay

/-! `NodeWire.current` changes no byte. The definitions below are the
strand serializers as they were before node terminators and the seal became
a parameter, copied verbatim; each equals its parameterized form at
`NodeWire.current` by `rfl`. The literal footers are checked separately in
`Tests.QueryCodec`. -/
namespace LfzkV2.Current.Tests.NodeWire
open CanonicalPrefix QueryRuntime

section Legacy
variable {Key Fresh Body : Type} {capacity : ℕ} (bodyCodec : PrefixCodec Body)

private def legacyHistoryFrom (roles : List Role) : (n : ℕ) → n ≤ roles.length →
    History Key (Block capacity Fresh) Digest n → Bytes → TranscriptV2.Strand.History
  | 0, _, _, message => .root message
  | n+1, within, previous, message =>
      .child (legacyHistoryFrom roles n (by omega) previous.1
        (previous.2.1.1.bytes ++ StrandQueryCodec.roundFooter (roles.get ⟨n,by omega⟩).domain))
        previous.2.2 message

private def legacyHistory {roles : List Role} : Input roles Key (Block capacity Fresh) Digest Body →
    TranscriptV2.Strand.History
  | .round i previous current => legacyHistoryFrom roles i.val (by omega) previous
      (current.1.bytes ++ StrandQueryCodec.roundFooter (roles.get i).domain)
  | .finalSeal previous body => legacyHistoryFrom roles roles.length le_rfl previous
      (StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode body))

private def legacyFinal : PrefixCodec {body // (bodyCodec.encode body).length ≤ maxLength} :=
  (framed bodyCodec).prefixed StrandQueryCodec.finalFooter

private def legacyEncode : (blocks : List QueryCodec.Block) → QueryCodec.Value bodyCodec.whole blocks →
    Bytes × List (Digest × Bytes)
  | [], body => ((legacyFinal bodyCodec).encode body,[])
  | block :: tail, value =>
      (block.codec.encode value.1 ++ StrandQueryCodec.roundFooter block.domain,
        match value.2 with
        | .inl _ => []
        | .inr (link,next) =>
            let later := legacyEncode tail next
            (link,later.1)::later.2)

private def legacyPacket {roles : List Role}
    (point : Input roles Key (Block capacity Fresh) Digest Body) : Bytes :=
  match point with
  | .round i _ current => current.1.bytes ++ StrandQueryCodec.roundFooter (roles.get i).domain
  | .finalSeal _ body => StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode body)

-- The verifier's node history, the online strand parser's encoder and the
-- linear-replay packets are the earlier functions.
example {roles : List Role} :
    (StrandRuntime.history NodeWire.current bodyCodec.whole :
        Input roles Key (Block capacity Fresh) Digest Body → _) = legacyHistory bodyCodec := by
  have round (n : ℕ) (within : n < roles.length) (previous : History Key (Block capacity Fresh) Digest n)
      (current : Block capacity Fresh) :
      StrandRuntime.history NodeWire.current bodyCodec.whole
          (.round ⟨n,within⟩ previous current : Input roles Key (Block capacity Fresh) Digest Body) =
        legacyHistory bodyCodec (.round ⟨n,within⟩ previous current) := by
    induction n generalizing current with
    | zero => rfl
    | succ n ih =>
        change TranscriptV2.Strand.History.child (StrandRuntime.history NodeWire.current bodyCodec.whole
            (.round ⟨n,by omega⟩ previous.1 previous.2.1 : Input roles Key (Block capacity Fresh) Digest Body))
            previous.2.2 _ =
          TranscriptV2.Strand.History.child (legacyHistory bodyCodec
            (.round ⟨n,by omega⟩ previous.1 previous.2.1 : Input roles Key (Block capacity Fresh) Digest Body))
            previous.2.2 _
        rw [ih]
        rfl
  funext point
  cases point with
  | round i previous current => exact round i.val i.isLt previous current
  | finalSeal previous body =>
      cases roles with
      | nil => rfl
      | cons role tail =>
          change TranscriptV2.Strand.History.child (StrandRuntime.history NodeWire.current bodyCodec.whole
              (.round ⟨tail.length,by simp⟩ previous.1 previous.2.1 :
                Input (role::tail) Key (Block capacity Fresh) Digest Body)) previous.2.2 _ =
            TranscriptV2.Strand.History.child (legacyHistory bodyCodec
              (.round ⟨tail.length,by simp⟩ previous.1 previous.2.1 :
                Input (role::tail) Key (Block capacity Fresh) Digest Body)) previous.2.2 _
          rw [round]
          rfl

example : StrandQueryCodec.encode NodeWire.current bodyCodec.whole = legacyEncode bodyCodec := by
  funext blocks
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
      funext value
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => rfl
      | inr next =>
          rcases next with ⟨link,next⟩
          simp only [StrandQueryCodec.encode,legacyEncode,ih]
          rfl

example {roles : List Role} :
    (StrandLinearReplay.packet NodeWire.current bodyCodec.whole :
        Input roles Key (Block capacity Fresh) Digest Body → _) = legacyPacket bodyCodec := by
  funext point
  cases point <;> rfl

end Legacy

-- The deployed closing bytes, literally.
example : NodeWire.current.terminator .sumcheck = frame roundDomain ++ frame [2] := by decide +kernel
example : NodeWire.current.sealFrame [9] = frame finalDomain ++ [0,1,0,0,0,0,0,0,0,9] := by decide +kernel
example : NodeWire.current.sealCodec.encode ⟨[9],by decide⟩ = NodeWire.current.sealFrame [9] := by
  decide +kernel

end LfzkV2.Current.Tests.NodeWire
