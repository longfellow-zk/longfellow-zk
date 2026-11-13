import LfzkV2.Current.ProofBodyCodec

/-! The current mdoc adapter has 768 shared bits and a 256-bit hiding value.
Its 1024 data leaves require ten quotient bits in each of two product trees.
Each tree's masked quotient is a separate `MaskedWord<10>`, an element of
GF(2)^10. Its canonical encoding is two little-endian bytes, least significant
bit first, and the six unused high bits must be zero.

The logical value is the pair of bounded ten-bit words itself. Its decoder
cannot reject a canonical value, and it does not accept a caller-supplied
meaning for the quotient bits. -/
namespace LfzkV2.Current.MdocAdvice
open TranscriptV2.Framing (Byte FieldCodec encodeLE readLE)

/-- One masked quotient word, `k xor o` for a ten-bit quotient and pad. -/
abbrev Word := Fin (2^10)

/-- The two masked quotients, one per conversion tree. -/
abbrev Value := Fin 2 → Word

def bits (value : Value) (tree : Fin 2) (index : Fin 10) : Bool :=
  (value tree).val.testBit index.val

/-- Each tree's word is decoded separately; there is no packing across trees. -/
theorem bit_position (value : Value) (tree : Fin 2) (index : Fin 10) :
    bits value tree index = (value tree).val.testBit index.val := rfl

/-- `MaskedWord::<10>::read`: two bytes, rejecting any nonzero padding bit.
Range checking the two-byte integer rejects precisely its unused high bits. -/
def word : PrefixCodec Word := PrefixCodec.unsigned 2 (2^10) (by decide)

theorem word_length (value : Word) : (word.encode value).length = 2 :=
  TranscriptV2.Framing.encodeLE_length _ _

/-- Both words, in tree order, with no separator or length word. -/
def codec : PrefixCodec Value := PrefixCodec.vector word 2

theorem encode_length (value : Value) : (codec.encode value).length = 4 := by
  rw [codec,PrefixCodec.vector_length word 2 word_length]

theorem encode_words (value : Value) :
    codec.encode value = encodeLE 2 (value 0).val ++ encodeLE 2 (value 1).val := by
  simp only [codec,PrefixCodec.vector_encode,List.ofFn_succ,List.ofFn_zero,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

theorem read_encode (value : Value) (suffix : Bytes) :
    codec.decode (codec.encode value ++ suffix) = some (value,suffix) :=
  codec.inverse value suffix

/-- Transcript writes: each masked word is its own `write_bytes`, framed by
the transcript's tag and eight-byte length. The domain label precedes them. -/
def writes : PrefixCodec Value :=
  PrefixCodec.vector (word.prefixed ([0] ++ encodeLE 8 2)) 2

theorem writes_length (value : Value) : (writes.encode value).length = 22 := by
  rw [writes,PrefixCodec.vector_length _ 11]
  intro v
  change (([0] ++ encodeLE 8 2) ++ word.encode v).length = 11
  rw [List.length_append,word_length]
  rfl

theorem writes_encode (value : Value) :
    writes.encode value = [0] ++ encodeLE 8 2 ++ encodeLE 2 (value 0).val ++
      ([0] ++ encodeLE 8 2 ++ encodeLE 2 (value 1).val) := by
  simp only [writes,PrefixCodec.vector_encode,List.ofFn_succ,List.ofFn_zero,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

/-- Advice has already passed its canonical range check at the proof-body
parser. Interpreting the accepted words is total. -/
def decode (value : Value) : Option (Fin 2 → Fin 10 → Bool) := some (bits value)

theorem decode_total (value : Value) : decode value = some (bits value) := rfl

theorem reject_high (input suffix : Bytes) (value : ℕ)
    (parsed : readLE 2 input = some (value,suffix)) (high : 2^10 ≤ value) :
    word.decode input = none := by
  simp only [word,PrefixCodec.unsigned,parsed,Option.bind_eq_bind,Option.bind_some]
  exact dif_neg (Nat.not_lt.mpr high)

/-- The word parser accepts all and only the runtime's canonical two-byte
words: the high byte keeps only its two low bits. -/
theorem decode_two_iff (low high : Byte) (suffix : Bytes) :
    (word.decode (low :: high :: suffix)).isSome ↔ high.val < 4 := by
  have hl := low.isLt
  simp only [word,PrefixCodec.unsigned,readLE,Option.bind_eq_bind,Option.bind_some]
  split <;> simp_all <;> omega

/-- Only the field scalar representations remain abstract. The current
mdoc advice representation and its exact byte widths are fixed here. -/
def representations {fields : Fields}
    (binary : FieldCodec (fields .binary)) (prime : FieldCodec (fields .prime))
    (binaryWidth : binary.width = 16) (primeWidth : prime.width = 32) :
    ProofBodyCodec.Representations fields Value where
  binary := binary
  prime := prime
  binaryWidth := binaryWidth
  primeWidth := primeWidth
  advice := codec
  adviceWidth := 4
  adviceLength := encode_length
  adviceWrites := writes
  adviceWritesWidth := 22
  adviceWritesLength := writes_length

end LfzkV2.Current.MdocAdvice
