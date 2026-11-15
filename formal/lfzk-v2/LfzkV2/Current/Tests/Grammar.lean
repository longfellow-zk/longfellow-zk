import LfzkV2.Current.Grammar
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Literal byte vectors for the node grammar over a two-field, two-tag
registry: every value kind, both terminators, and the rejections that make
parsing canonical (reserved and unknown tags, wrong kind words, unknown field
IDs, nonzero bit padding, a node without a message). -/
namespace LfzkV2.Current.Tests.Grammar
open TranscriptV2.Framing (Byte FieldCodec)
open LfzkV2.Current.Grammar

private def rawField (width : ℕ) (positive : 0 < width) (buffer : width ≤ 128) :
    FieldCodec (Fin width → Byte) where
  width := width
  positive := positive
  buffer := buffer
  encode := (PrefixCodec.vector PrefixCodec.byte width).encode
  decode bytes := do
    let (value,rest) ← (PrefixCodec.vector PrefixCodec.byte width).decode bytes
    if rest = [] then some value else none
  length value := by rw [PrefixCodec.bytes_encode,List.length_ofFn]
  inverse value := by
    have hi := (PrefixCodec.vector PrefixCodec.byte width).inverse value []
    simp only [List.append_nil] at hi
    simp [hi]
  canonical bytes value h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨decoded,rest⟩,hd,h⟩ := h
    split at h
    · rename_i hr
      cases Option.some.inj h
      have hc := (PrefixCodec.vector PrefixCodec.byte width).canonical bytes decoded rest hd
      change rest = [] at hr
      rw [hr,List.append_nil] at hc
      exact hc.symm
    · contradiction

/-- Field ID 1 has two-byte elements, field ID 2 one-byte elements. -/
private abbrev fields : FieldTable where
  Id := Bool
  code field := if field then 2 else 1
  ofCode word := if word.val = 1 then some false else if word.val = 2 then some true else none
  ofCode_code field := by cases field <;> rfl
  code_ofCode word field h := by
    split at h
    next h1 => cases h; exact Fin.ext h1.symm
    next =>
      split at h
      next h2 => cases h; exact Fin.ext h2.symm
      next => contradiction
  Element field := match field with
    | false => Fin 2 → Byte
    | true => Fin 1 → Byte
  codec field := match field with
    | false => rawField 2 (by decide) (by decide)
    | true => rawField 1 (by decide) (by decide)

private inductive Tag where
  | statement | round
  deriving DecidableEq, Repr

private abbrev registry : Registry where
  Tag := Tag
  code tag := match tag with | .statement => 16 | .round => 48
  ofCode word := if word.val = 16 then some .statement else if word.val = 48 then some .round else none
  ofCode_code tag := by cases tag <;> rfl
  code_ofCode word tag h := by
    split at h
    next h16 => cases h; exact Fin.ext h16.symm
    next =>
      split at h
      next h48 => cases h; exact Fin.ext h48.symm
      next => contradiction
  reserved tag := by cases tag <;> decide
  schema tag := match tag with
    | .statement => [.bytes,.nats]
    | .round => [.elements,.bits]

private def word (value : Byte) : Bytes := [value,0,0,0,0,0,0,0]

private def statement : Message fields registry :=
  ⟨.statement,(⟨[5,6],by decide⟩,(⟨[3],by decide⟩,()))⟩

private def round : Message fields registry :=
  ⟨.round,(⟨false,⟨[![7,8]],by decide⟩⟩,(⟨[true,false,true],by decide⟩,()))⟩

private def first : Node fields registry := ⟨[statement,round],by simp,.round⟩
private def sealed : Node fields registry := ⟨[round],by simp,.seal⟩

private def statementBytes : Bytes :=
  word 16 ++ (word 0 ++ word 2 ++ [5,6]) ++ (word 1 ++ word 1 ++ word 3)

private def roundBytes : Bytes :=
  word 48 ++ (word 2 ++ word 1 ++ word 1 ++ [7,8]) ++ (word 3 ++ word 3 ++ [0b101])

private def firstBytes : Bytes := statementBytes ++ roundBytes ++ word 0
private def sealedBytes : Bytes := roundBytes ++ word 1

-- Every integer is a u64 word; each value carries its kind and count.
example : (message fields registry).encode statement = statementBytes := by decide +kernel
example : (message fields registry).encode round = roundBytes := by decide +kernel

private theorem first_encode : (node fields registry).encode first = firstBytes := by decide +kernel
private theorem sealed_encode : (node fields registry).encode sealed = sealedBytes := by decide +kernel

example : (node fields registry).decode (firstBytes ++ sealedBytes) = some (first,sealedBytes) := by
  rw [← first_encode]
  exact (node fields registry).inverse _ _

-- The decoder alone recovers the tags, the terminator and the unread suffix.
example : ((node fields registry).decode (firstBytes ++ [9])).map
    (fun decoded => (decoded.1.messages.map Sigma.fst,decoded.1.terminal,decoded.2)) =
      some ([.statement,.round],.round,[9]) := by decide +kernel
example : ((node fields registry).decode sealedBytes).map
    (fun decoded => (decoded.1.messages.map Sigma.fst,decoded.1.terminal,decoded.2)) =
      some ([.round],.seal,[]) := by decide +kernel

-- Bits: ceil(count/8) bytes, least significant first.
example : (value fields .bits).encode ⟨[],by decide⟩ = word 3 ++ word 0 := by decide +kernel
example : (value fields .bits).encode ⟨List.replicate 8 true,by decide⟩ = word 3 ++ word 8 ++ [255] := by
  decide +kernel
example : (value fields .bits).encode ⟨List.replicate 8 false ++ [true],by decide⟩ =
    word 3 ++ word 9 ++ [0,1] := by decide +kernel

-- Nonzero padding has no preimage.
example : ((value fields .bits).decode (word 3 ++ word 3 ++ [0b1101])).isNone := by decide +kernel
-- A node needs a message.
example : ((node fields registry).decode (word 0)).isNone := by decide +kernel
-- Words 2..15 are reserved terminators, and 17 is not a registered tag.
example : ((node fields registry).decode (roundBytes ++ word 2)).isNone := by decide +kernel
example : ((node fields registry).decode (word 17 ++ word 0)).isNone := by decide +kernel
-- The tag fixes the kinds: Nats where the schema has Bytes.
example : ((node fields registry).decode
    (word 16 ++ (word 1 ++ word 0) ++ (word 1 ++ word 0) ++ word 0)).isNone := by decide +kernel
-- Elements of an unknown field ID.
example : ((node fields registry).decode
    (word 48 ++ (word 2 ++ word 9 ++ word 0) ++ (word 3 ++ word 0) ++ word 0)).isNone := by decide +kernel
-- The field ID fixes the element width: field 2 reads one byte per element.
example : ((value fields .elements).decode (word 2 ++ word 2 ++ word 1 ++ [7,8])).map Prod.snd =
    some [8] := by decide +kernel

-- A whole transcript of nodes is injective.
example (left right : List (Node fields registry))
    (same : left.flatMap (node fields registry).encode = right.flatMap (node fields registry).encode) :
    left = right := nodes_injective fields registry same

/--
info: 'LfzkV2.Current.Grammar.nodes_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.Grammar.nodes_injective

end LfzkV2.Current.Tests.Grammar
