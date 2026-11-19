import LfzkV2.Current.QueryCodec
import LfzkV2.Current.NodeWire
import TranscriptV2.StrandUnfolding

/-! Parse recovered strand histories using the existing canonical packet
schemas. Packet data contains only actual writes; cached runtime fields are
reconstructed by the packet embedding (`QueryPacket`). No codec for arbitrary
redundant runtime caches is assumed. Node terminators and the seal come from
a `NodeWire`; the endpoints use `TaggedFormat.wire`. -/
noncomputable section
namespace LfzkV2.Current.StrandQueryCodec
open CanonicalPrefix
open scoped Classical

variable {Body : Type} (wire : NodeWire) (bodyCodec : WholeCodec Body)

private def final : PrefixCodec {body // (bodyCodec.encode body).length ≤ maxLength} :=
  wire.sealed bodyCodec

private def readBlock (block : QueryCodec.Block) (input : Bytes) : Option block.Data := do
  let (value,rest) ← block.codec.decode input
  if rest = wire.terminator block.domain then some value else none

private theorem readBlock_encode (block : QueryCodec.Block) (value : block.Data) :
    readBlock wire block (block.codec.encode value ++ wire.terminator block.domain) = some value := by
  simp only [readBlock,block.codec.inverse,Option.bind_eq_bind,Option.bind_some,if_true]

private theorem readBlock_canonical (block : QueryCodec.Block) (input : Bytes) (value : block.Data)
    (found : readBlock wire block input = some value) : input = block.codec.encode value ++ wire.terminator block.domain := by
  simp only [readBlock,Option.bind_eq_bind,Option.bind_eq_some_iff] at found
  obtain ⟨⟨decoded,rest⟩,parsed,result⟩ := found
  split at result
  next equal =>
    cases Option.some.inj result
    change rest = wire.terminator block.domain at equal
    simpa only [equal] using block.codec.canonical input decoded rest parsed
  next _ => contradiction

/-- Canonical packet values determine the root payload and every later
one-parent payload. Links are the parents' digests; they add no payload bytes. -/
def encode : (blocks : List QueryCodec.Block) → QueryCodec.Value bodyCodec blocks →
    Bytes × List (Digest × Bytes)
  | [], body => ((final wire bodyCodec).encode body,[])
  | block :: tail, value =>
      (block.codec.encode value.1 ++ wire.terminator block.domain,
        match value.2 with
        | .inl _ => []
        | .inr (link,next) =>
            let later := encode tail next
            (link,later.1)::later.2)

def decode : (blocks : List QueryCodec.Block) → Bytes × List (Digest × Bytes) →
    Option (QueryCodec.Value bodyCodec blocks)
  | [], (input,[]) => readWhole (final wire bodyCodec) input
  | [], (_, _::_) => none
  | block :: tail, (input,rest) => do
      let value ← readBlock wire block input
      match rest with
      | [] => some (value,.inl ())
      | (link,next)::rest => do
          let parsed ← decode tail (next,rest)
          some (value,.inr (link,parsed))

theorem decode_encode (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    decode wire bodyCodec blocks (encode wire bodyCodec blocks value) = some value := by
  induction blocks with
  | nil => exact readWhole_encode _ value
  | cons block tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => cases stop; simp only [encode,decode,readBlock_encode,Option.bind_eq_bind,Option.bind_some]
      | inr next =>
          rcases next with ⟨link,next⟩
          simp only [encode,decode,readBlock_encode,Option.bind_eq_bind,Option.bind_some,ih]

theorem encode_decode (blocks : List QueryCodec.Block) (input : Bytes × List (Digest × Bytes))
    (value : QueryCodec.Value bodyCodec blocks) (found : decode wire bodyCodec blocks input = some value) :
    encode wire bodyCodec blocks value = input := by
  induction blocks generalizing input with
  | nil =>
      rcases input with ⟨input,rest⟩
      cases rest with
      | nil => exact Prod.ext (readWhole_canonical _ input value found).symm rfl
      | cons _ _ => cases found
  | cons block tail ih =>
      rcases input with ⟨input,rest⟩
      simp only [decode,Option.bind_eq_bind,Option.bind_eq_some_iff] at found
      obtain ⟨current,parsed,found⟩ := found
      have canonical := readBlock_canonical wire block input current parsed
      cases rest with
      | nil =>
          cases Option.some.inj found
          exact Prod.ext canonical.symm rfl
      | cons step rest =>
          rcases step with ⟨link,next⟩
          obtain ⟨later,parsed,result⟩ := Option.bind_eq_some_iff.mp found
          cases Option.some.inj result
          have laterEq := ih (next,rest) later parsed
          simp only [encode,laterEq]
          exact Prod.ext canonical.symm rfl

/-- The node payloads determine the packet values when each node's payload
determines its packet value, without the parser: this is how a node grammar
(`TaggedGrammar`) yields the injectivity of canonical points. -/
theorem encode_injective (blocks : List QueryCodec.Block)
    (nodes : ∀ block ∈ blocks, Function.Injective fun value : block.Data =>
      block.codec.encode value ++ wire.terminator block.domain)
    (sealed : Function.Injective (wire.sealed bodyCodec).encode) :
    Function.Injective (encode wire bodyCodec blocks) := by
  induction blocks with
  | nil =>
      intro first second same
      exact sealed (congrArg Prod.fst same)
  | cons block tail ih =>
      intro first second same
      rcases first with ⟨first,firstNext⟩
      rcases second with ⟨second,secondNext⟩
      have head := nodes block List.mem_cons_self (congrArg Prod.fst same)
      subst head
      have rest := congrArg Prod.snd same
      cases firstNext with
      | inl stop =>
          cases secondNext with
          | inl other => cases stop; cases other; rfl
          | inr next => simp only [encode] at rest; cases rest
      | inr firstLater =>
          rcases firstLater with ⟨firstLink,firstNext⟩
          cases secondNext with
          | inl other => simp only [encode] at rest; cases rest
          | inr secondLater =>
              rcases secondLater with ⟨secondLink,secondNext⟩
              simp only [encode,List.cons.injEq,Prod.mk.injEq] at rest
              obtain ⟨⟨rfl,hfirst⟩,hrest⟩ := rest
              have later := ih (fun block mem => nodes block (List.mem_cons_of_mem _ mem))
                (Prod.ext hfirst hrest)
              rw [later]

def toHistory (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    TranscriptV2.Strand.History :=
  let encoded := encode wire bodyCodec blocks value
  .ofSpine encoded.1 encoded.2

def fromHistory (blocks : List QueryCodec.Block) (history : TranscriptV2.Strand.History) :
    Option (QueryCodec.Value bodyCodec blocks) := decode wire bodyCodec blocks history.spine

theorem fromHistory_toHistory (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    fromHistory wire bodyCodec blocks (toHistory wire bodyCodec blocks value) = some value := by
  simp only [fromHistory,toHistory,TranscriptV2.Strand.History.spine_ofSpine,Prod.eta,decode_encode]

theorem fromHistory_canonical (blocks : List QueryCodec.Block) (history : TranscriptV2.Strand.History)
    (value : QueryCodec.Value bodyCodec blocks) (found : fromHistory wire bodyCodec blocks history = some value) :
    toHistory wire bodyCodec blocks value = history := by
  have encoded := encode_decode wire bodyCodec blocks history.spine value found
  simp only [toHistory,encoded,TranscriptV2.Strand.History.ofSpine_spine]

/-- The concrete packet parser supplies the schema used by online query
renaming. Its inverse laws are proved from the component codecs. -/
def schema (blocks : List QueryCodec.Block) :
    TranscriptV2.Strand.History.Codec (QueryCodec.Value bodyCodec blocks) where
  encode := toHistory wire bodyCodec blocks
  decode := fromHistory wire bodyCodec blocks
  inverse := fromHistory_toHistory wire bodyCodec blocks
  canonical := fromHistory_canonical wire bodyCodec blocks

/-- Remove the last node from a canonical packet history. The first
boundary has no parent, and later boundaries retain the same first packet. -/
def parent : (blocks : List QueryCodec.Block) → QueryCodec.Value bodyCodec blocks →
    Option (QueryCodec.Value bodyCodec blocks)
  | [], _ => none
  | _ :: _, (_, .inl _) => none
  | _ :: tail, (value, .inr (link,next)) =>
      some (value,match parent tail next with
        | none => .inl ()
        | some earlier => .inr (link,earlier))

theorem parent_first (block : QueryCodec.Block) (tail : List QueryCodec.Block)
    (value earlier : QueryCodec.Value bodyCodec (block::tail))
    (previous : parent bodyCodec (block::tail) value = some earlier) : value.1 = earlier.1 := by
  rcases value with ⟨value,next⟩
  cases next with
  | inl stop => cases previous
  | inr next =>
      rcases next with ⟨link,next⟩
      simp only [parent] at previous
      have equal := Option.some.inj previous
      have projected := congrArg (fun (point : QueryCodec.Value bodyCodec (block::tail)) => point.1) equal
      exact projected

theorem history_continue (block : QueryCodec.Block) (tail : List QueryCodec.Block)
    (value : block.Data) (link : Digest) (next : QueryCodec.Value bodyCodec tail) :
    toHistory wire bodyCodec (block::tail) (value,.inr (link,next)) =
      (toHistory wire bodyCodec tail next).prepend (block.codec.encode value ++ wire.terminator block.domain) link := by
  simp only [toHistory,encode,TranscriptV2.Strand.History.prepend_ofSpine]

theorem history_without_parent (blocks : List QueryCodec.Block)
    (value : QueryCodec.Value bodyCodec blocks) (first : parent bodyCodec blocks value = none) :
    ∃ message, toHistory wire bodyCodec blocks value = .root message := by
  cases blocks with
  | nil => exact ⟨_,rfl⟩
  | cons block tail =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => exact ⟨_,rfl⟩
      | inr next => cases first

theorem history_parent (blocks : List QueryCodec.Block)
    (child earlier : QueryCodec.Value bodyCodec blocks)
    (previous : parent bodyCodec blocks child = some earlier) :
    ∃ digest message, toHistory wire bodyCodec blocks child =
      .child (toHistory wire bodyCodec blocks earlier) digest message := by
  induction blocks with
  | nil => cases previous
  | cons block tail ih =>
      rcases child with ⟨value,next⟩
      cases next with
      | inl stop => cases previous
      | inr next =>
          rcases next with ⟨link,next⟩
          cases found : parent bodyCodec tail next with
          | none =>
              have equal : ((value,Sum.inl ()) : QueryCodec.Value bodyCodec (block::tail)) = earlier := by
                simpa only [parent,found,Option.some.injEq,QueryCodec.Value] using previous
              subst earlier
              obtain ⟨message,shape⟩ := history_without_parent wire bodyCodec tail next found
              rw [history_continue,shape]
              exact ⟨link,message,rfl⟩
          | some prior =>
              have equal : ((value,Sum.inr (link,prior)) : QueryCodec.Value bodyCodec (block::tail)) = earlier := by
                simpa only [parent,found,Option.some.injEq,QueryCodec.Value] using previous
              subst earlier
              obtain ⟨digest,message,shape⟩ := ih next prior found
              rw [history_continue,shape]
              exact ⟨digest,message,congrArg (fun history => TranscriptV2.Strand.History.child history digest message)
                (history_continue wire bodyCodec block tail value link prior).symm⟩

end LfzkV2.Current.StrandQueryCodec
