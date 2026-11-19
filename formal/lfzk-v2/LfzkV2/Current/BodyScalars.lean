import LfzkV2.Current.ByteCodecs
import LfzkV2.Current.Messages

/-! The scalar and advice representations a proof format writes: field
element codecs and the advice codecs. The proof body, the transcript and the
Merkle leaves all use them. -/
namespace LfzkV2.Current.ProofBodyCodec
open TranscriptV2.Framing (FieldCodec)

variable {fields : Fields} {Advice : Type}

/-- Raw scalar and fixed-size canonical advice representations. Scalar
bytes carry no transcript-operation tags inside the proof body. -/
structure Representations (fields : Fields) (Advice : Type) where
  binary : FieldCodec (fields .binary)
  prime : FieldCodec (fields .prime)
  binaryWidth : binary.width = 16
  primeWidth : prime.width = 32
  advice : PrefixCodec Advice
  adviceWidth : ℕ
  adviceLength : ∀ value, (advice.encode value).length = adviceWidth
  /-- The transcript writes of the same advice after its domain label. Each
  masked word is its own framed `write_bytes`; no derived value is written. -/
  adviceWrites : PrefixCodec Advice
  adviceWritesWidth : ℕ
  adviceWritesLength : ∀ value, (adviceWrites.encode value).length = adviceWritesWidth

end LfzkV2.Current.ProofBodyCodec
