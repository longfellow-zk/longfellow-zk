import LfzkV2.Current.ProofBodyCodec

/-! The current mdoc adapter has 768 shared bits and a 256-bit hiding value.
Its 1024 leaves require ten quotient bits in each of two product trees.
The proof stores those twenty bits consecutively, least significant bit first,
in three bytes. The unused four high bits must be zero.

The logical value is the bounded twenty-bit word itself. Its decoder cannot
reject a canonical value, and it does not accept a caller-supplied meaning
for the quotient bits. -/
namespace LfzkV2.Current.MdocAdvice
open TranscriptV2.Framing (Byte FieldCodec encodeLE readLE)

abbrev Value := Fin (2^20)

def bits (value : Value) (tree : Fin 2) (index : Fin 10) : Bool :=
  value.val.testBit (10*tree.val+index.val)

/-- The first tree occupies bits 0 through 9; the second occupies 10 through
19. This is the order used by the runtime's byte-to-bit loop. -/
theorem bit_position (value : Value) (tree : Fin 2) (index : Fin 10) :
    bits value tree index = value.val.testBit (10*tree.val+index.val) := rfl

/-- Range checking the three-byte integer rejects precisely its unused
high bits. No serialized padding is added. -/
def codec : PrefixCodec Value := PrefixCodec.unsigned 3 (2^20) (by decide)

theorem encode_length (value : Value) : (codec.encode value).length = 3 :=
  TranscriptV2.Framing.encodeLE_length _ _

theorem encode_word (value : Value) : codec.encode value = encodeLE 3 value.val := rfl

theorem read_encode (value : Value) (suffix : Bytes) :
    codec.decode (codec.encode value ++ suffix) = some (value,suffix) :=
  codec.inverse value suffix

/-- Advice has already passed its canonical range check at the proof-body
parser. Interpreting the accepted word is total. -/
def decode (value : Value) : Option (Fin 2 → Fin 10 → Bool) := some (bits value)

theorem decode_total (value : Value) : decode value = some (bits value) := rfl

theorem reject_high (input suffix : Bytes) (word : ℕ)
    (parsed : readLE 3 input = some (word,suffix)) (high : 2^20 ≤ word) :
    codec.decode input = none := by
  simp only [codec,PrefixCodec.unsigned,parsed,Option.bind_eq_bind,Option.bind_some]
  exact dif_neg (Nat.not_lt.mpr high)

/-- The byte parser accepts all and only the runtime's canonical three-byte
words. In particular, there is no extra restriction on either quotient. -/
theorem decode_three_iff (low middle high : Byte) (suffix : Bytes) :
    (codec.decode (low :: middle :: high :: suffix)).isSome ↔ high.val < 16 := by
  have hl := low.isLt
  have hm := middle.isLt
  simp only [codec,PrefixCodec.unsigned,readLE,Option.bind_eq_bind,Option.bind_some]
  split <;> simp_all <;> omega

/-- Only the field scalar representations remain abstract. The current
mdoc advice representation and its exact byte width are fixed here. -/
def representations {fields : Fields}
    (binary : FieldCodec (fields .binary)) (prime : FieldCodec (fields .prime))
    (binaryWidth : binary.width = 16) (primeWidth : prime.width = 32) :
    ProofBodyCodec.Representations fields Value where
  binary := binary
  prime := prime
  binaryWidth := binaryWidth
  primeWidth := primeWidth
  advice := codec
  adviceWidth := 3
  adviceLength := encode_length

end LfzkV2.Current.MdocAdvice
