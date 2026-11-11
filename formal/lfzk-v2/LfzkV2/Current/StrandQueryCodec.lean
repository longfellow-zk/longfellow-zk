import LfzkV2.Current.QueryCodec
import TranscriptV2.StrandUnfolding

/-! Parse recovered strand histories using the existing canonical packet
schemas. Packet data contains only actual writes; cached runtime fields are
reconstructed by the existing QueryRuntime embedding. No codec for arbitrary
redundant runtime caches is assumed. -/
noncomputable section
namespace LfzkV2.Current.StrandQueryCodec
open CanonicalPrefix
open scoped Classical

variable {Body : Type} (bodyCodec : PrefixCodec Body)

def roundFooter (domain : Domain) : Bytes :=
  frame roundDomain ++ frame [label domain]

def finalFooter : Bytes := frame finalDomain

private def final : PrefixCodec {body // (bodyCodec.encode body).length ≤ maxLength} :=
  (framed bodyCodec).prefixed finalFooter

private def readBlock (block : QueryCodec.Block) (input : Bytes) : Option block.Data := do
  let (value,rest) ← block.codec.decode input
  if rest = roundFooter block.domain then some value else none

private theorem readBlock_encode (block : QueryCodec.Block) (value : block.Data) :
    readBlock block (block.codec.encode value ++ roundFooter block.domain) = some value := by
  simp only [readBlock,block.codec.inverse,Option.bind_eq_bind,Option.bind_some,if_true]

private theorem readBlock_canonical (block : QueryCodec.Block) (input : Bytes) (value : block.Data)
    (found : readBlock block input = some value) : input = block.codec.encode value ++ roundFooter block.domain := by
  simp only [readBlock,Option.bind_eq_bind,Option.bind_eq_some_iff] at found
  obtain ⟨⟨decoded,rest⟩,parsed,result⟩ := found
  split at result
  next equal =>
    cases Option.some.inj result
    change rest = roundFooter block.domain at equal
    simpa only [equal] using block.codec.canonical input decoded rest parsed
  next _ => contradiction

/-- Canonical packet values determine the root payload and every later
one-parent payload. Round counters and feedback framing add no wire bytes. -/
def encode : (blocks : List QueryCodec.Block) → QueryCodec.Value bodyCodec blocks →
    Bytes × List (Digest × Bytes)
  | [], body => ((final bodyCodec).encode body,[])
  | block :: tail, value =>
      (block.codec.encode value.1 ++ roundFooter block.domain,
        match value.2 with
        | .inl _ => []
        | .inr (link,next) =>
            let later := encode tail next
            (link,later.1)::later.2)

def decode : (blocks : List QueryCodec.Block) → Bytes × List (Digest × Bytes) →
    Option (QueryCodec.Value bodyCodec blocks)
  | [], (input,[]) => readWhole (final bodyCodec) input
  | [], (_, _::_) => none
  | block :: tail, (input,rest) => do
      let value ← readBlock block input
      match rest with
      | [] => some (value,.inl ())
      | (link,next)::rest => do
          let parsed ← decode tail (next,rest)
          some (value,.inr (link,parsed))

theorem decode_encode (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    decode bodyCodec blocks (encode bodyCodec blocks value) = some value := by
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
    (value : QueryCodec.Value bodyCodec blocks) (found : decode bodyCodec blocks input = some value) :
    encode bodyCodec blocks value = input := by
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
      have canonical := readBlock_canonical block input current parsed
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

def toHistory (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    TranscriptV2.Strand.History :=
  let encoded := encode bodyCodec blocks value
  .ofSpine encoded.1 encoded.2

def fromHistory (blocks : List QueryCodec.Block) (history : TranscriptV2.Strand.History) :
    Option (QueryCodec.Value bodyCodec blocks) := decode bodyCodec blocks history.spine

theorem fromHistory_toHistory (blocks : List QueryCodec.Block) (value : QueryCodec.Value bodyCodec blocks) :
    fromHistory bodyCodec blocks (toHistory bodyCodec blocks value) = some value := by
  simp only [fromHistory,toHistory,TranscriptV2.Strand.History.spine_ofSpine,Prod.eta,decode_encode]

theorem fromHistory_canonical (blocks : List QueryCodec.Block) (history : TranscriptV2.Strand.History)
    (value : QueryCodec.Value bodyCodec blocks) (found : fromHistory bodyCodec blocks history = some value) :
    toHistory bodyCodec blocks value = history := by
  have encoded := encode_decode bodyCodec blocks history.spine value found
  simp only [toHistory,encoded,TranscriptV2.Strand.History.ofSpine_spine]

/-- The concrete packet parser supplies the schema used by online query
renaming. Its inverse laws are proved from the component codecs. -/
def schema (blocks : List QueryCodec.Block) :
    TranscriptV2.Strand.History.Codec (QueryCodec.Value bodyCodec blocks) where
  encode := toHistory bodyCodec blocks
  decode := fromHistory bodyCodec blocks
  inverse := fromHistory_toHistory bodyCodec blocks
  canonical := fromHistory_canonical bodyCodec blocks

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
    toHistory bodyCodec (block::tail) (value,.inr (link,next)) =
      (toHistory bodyCodec tail next).prepend (block.codec.encode value ++ roundFooter block.domain) link := by
  simp only [toHistory,encode,TranscriptV2.Strand.History.prepend_ofSpine]

theorem history_without_parent (blocks : List QueryCodec.Block)
    (value : QueryCodec.Value bodyCodec blocks) (first : parent bodyCodec blocks value = none) :
    ∃ message, toHistory bodyCodec blocks value = .root message := by
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
    ∃ digest message, toHistory bodyCodec blocks child =
      .child (toHistory bodyCodec blocks earlier) digest message := by
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
              obtain ⟨message,shape⟩ := history_without_parent bodyCodec tail next found
              rw [history_continue,shape]
              exact ⟨link,message,rfl⟩
          | some prior =>
              have equal : ((value,Sum.inr (link,prior)) : QueryCodec.Value bodyCodec (block::tail)) = earlier := by
                simpa only [parent,found,Option.some.injEq,QueryCodec.Value] using previous
              subst earlier
              obtain ⟨digest,message,shape⟩ := ih next prior found
              rw [history_continue,shape]
              exact ⟨digest,message,congrArg (fun history => TranscriptV2.Strand.History.child history digest message)
                (history_continue bodyCodec block tail value link prior).symm⟩

end LfzkV2.Current.StrandQueryCodec
