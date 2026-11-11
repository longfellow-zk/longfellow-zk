import Merkle.Indexed.Commit

/-! The index is supplied by the heap traversal, not trusted from an opening.
Decoding an internal input must check that exact expected position. -/
namespace Merkle.Indexed

universe uSalt uMsg uDigest uEnc
variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest} {Enc : Type uEnc}

structure RoleDecoders (codec : Codec Salt M D Enc) where
  leafDec : Enc → Option (Salt × M)
  nodeDec : ℕ → Enc → Option (D × D)
  leaf_roundTrip : ∀ value, leafDec (codec.leafEnc value) = some value
  node_roundTrip : ∀ index value, nodeDec index (codec.nodeEnc index value) = some value
  leaf_sound : ∀ raw value, leafDec raw = some value → codec.leafEnc value = raw
  node_sound : ∀ index raw value, nodeDec index raw = some value → codec.nodeEnc index value = raw

theorem RoleDecoders.inj {codec : Codec Salt M D Enc} (dec : RoleDecoders codec) : codec.Inj := by
  constructor
  · intro first second same
    have decoded := congrArg dec.leafDec same
    rw [dec.leaf_roundTrip,dec.leaf_roundTrip] at decoded
    exact Option.some.inj decoded
  · intro index first second same
    have decoded := congrArg (dec.nodeDec index) same
    rw [dec.node_roundTrip,dec.node_roundTrip] at decoded
    exact Option.some.inj decoded

end Merkle.Indexed
