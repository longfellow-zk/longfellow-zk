import LfzkV2.Current.CanonicalPrefix
import TranscriptV2.StrandTranscript

/-! The bytes that close a strand node, as a parameter of the strand
codecs. A node at a challenge boundary ends with its terminator; the final
node is the seal applied to the complete proof body. The deployed wire is
`TaggedFormat.wire`. -/
namespace LfzkV2.Current
open CanonicalPrefix

/-- Node closing bytes. A terminator is a fixed marker for its boundary
domain; the codecs read it back by comparison, so they need no law about
it. The seal frames an arbitrary body for the verifier's history, and its
codec parses that frame back on bounded bodies. -/
structure NodeWire where
  terminator : Domain → Bytes
  sealFrame : Bytes → Bytes
  sealCodec : PrefixCodec (BoundedBytes maxLength)
  sealCodec_encode : ∀ body, sealCodec.encode body = sealFrame body.bytes

namespace NodeWire
variable (wire : NodeWire) {A : Type}

/-- The final node payload of a canonical body. The parser rejects bytes
left over inside the sealed frame. -/
def sealed (codec : WholeCodec A) :
    PrefixCodec {value // (codec.encode value).length ≤ maxLength} where
  encode value := wire.sealCodec.encode ⟨codec.encode value.val,value.property⟩
  decode input := do
    let (payload,suffix) ← wire.sealCodec.decode input
    match h : codec.decode payload.bytes with
    | none => none
    | some value => some (⟨value,by
        rw [← codec.canonical payload.bytes value h]
        exact payload.bound⟩,suffix)
  inverse value suffix := by
    simp only [wire.sealCodec.inverse,Option.bind_eq_bind,Option.bind_some]
    split
    · rename_i hn
      have hi := codec.inverse value.val
      rw [hn] at hi
      contradiction
    · rename_i decoded hd
      have he : decoded = value.val := Option.some.inj (hd.symm.trans (codec.inverse value.val))
      subst decoded
      rfl
  canonical input value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨payload,rest⟩,hp,h⟩ := h
    split at h
    · contradiction
    · rename_i decoded hd
      cases Option.some.inj h
      have he := codec.canonical payload.bytes decoded hd
      have hb : (codec.encode decoded).length ≤ maxLength := by rw [← he]; exact payload.bound
      have hs : payload = (⟨codec.encode decoded,hb⟩ : BoundedBytes maxLength) := BoundedBytes.ext he
      calc
        input = wire.sealCodec.encode payload ++ rest := wire.sealCodec.canonical input payload rest hp
        _ = wire.sealCodec.encode ⟨codec.encode decoded,hb⟩ ++ rest := by rw [hs]
        _ = _ := rfl

theorem sealed_encode (codec : WholeCodec A)
    (value : {value // (codec.encode value).length ≤ maxLength}) :
    (wire.sealed codec).encode value = wire.sealFrame (codec.encode value.val) :=
  wire.sealCodec_encode _

end NodeWire
end LfzkV2.Current
