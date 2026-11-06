import TranscriptV2.FramingSound

namespace TranscriptV2.Tests.Framing
open TranscriptV2.Framing

private def byteCodec : FieldCodec Byte where
  width := 1
  positive := by decide
  buffer := by decide
  encode value := [value]
  decode
    | [value] => some value
    | _ => none
  length _ := rfl
  inverse _ := rfl
  canonical payload value h := by
    cases payload with
    | nil => cases h
    | cons head tail =>
        cases tail with
        | nil => cases Option.some.inj h; rfl
        | cons => cases h

private abbrev Field (_ : Unit) := Byte
private def codecs (_ : Unit) : FieldCodec Byte := byteCodec
private def schema : List (Kind Unit) := [.bytes,.scalar (),.slice ()]
private def values : Values Field schema := ([0,1],(255,([3,4],())))
private def encoded : Bytes :=
  [0,2,0,0,0,0,0,0,0,0,1, 1,255, 2,2,0,0,0,0,0,0,0,3,4]

-- Exact Rust byte/scalar/slice tags and little-endian lengths.
example : encodeValues Field codecs schema values = encoded := rfl
example : decodeValues Field codecs schema (encoded ++ [9,8]) = some (values,[9,8]) := rfl

-- Truncation and a wrong operation tag reject before consuming a continuation.
example : decode Field codecs (.scalar ()) [2,255] = none := rfl
example : decode Field codecs (.slice ()) [2,3,0,0,0,0,0,0,0,3,4] = none := rfl
example : decode Field codecs .bytes [0,2,0,0,0,0,0,0,0,7] = none := rfl

example : encodeLE 8 (2^64-1) = List.replicate 8 255 := by decide

-- The u64 validity bound is essential when encoding a host-length integer.
example : encodeLE 8 (2^64) = encodeLE 8 0 := by decide

private def pairCodec : FieldCodec (Byte × Byte) where
  width := 2
  positive := by decide
  buffer := by decide
  encode value := [value.1,value.2]
  decode
    | [first,second] => some (first,second)
    | _ => none
  length _ := rfl
  inverse _ := rfl
  canonical payload value h := by
    cases payload with
    | nil => cases h
    | cons first tail =>
        cases tail with
        | nil => cases h
        | cons second tail =>
            cases tail with
            | nil => cases Option.some.inj h; rfl
            | cons => cases h

private abbrev MixedField : Bool → Type
  | false => Byte
  | true => Byte × Byte
private def mixedCodecs : (i : Bool) → FieldCodec (MixedField i)
  | false => byteCodec
  | true => pairCodec
private def shortFirst : List (Kind Bool) := [.scalar false,.scalar true]
private def wideFirst : List (Kind Bool) := [.scalar true,.scalar false]
private def shortValues : Values MixedField shortFirst := (1,((1,2),()))
private def wideValues : Values MixedField wideFirst := ((1,1),(2,()))

-- Scalar frames carry no field identifier. Each fixed public schema recovers
-- its own fields, even though two different schemas can encode the same bytes.
example : encodeValues MixedField mixedCodecs shortFirst shortValues =
    encodeValues MixedField mixedCodecs wideFirst wideValues := rfl
example : decodeValues MixedField mixedCodecs shortFirst [1,1,1,1,2] = some (shortValues,[]) := rfl
example : decodeValues MixedField mixedCodecs wideFirst [1,1,1,1,2] = some (wideValues,[]) := rfl

end TranscriptV2.Tests.Framing
