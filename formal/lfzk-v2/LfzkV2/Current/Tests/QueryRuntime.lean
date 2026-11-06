import LfzkV2.Current.QueryRuntime

/-! Canonical query parsing reconstructs the logical context and caches.
Changing either redundant value creates a malformed typed alias, even
though erasing that alias would leave the physical query unchanged. -/
noncomputable section
namespace LfzkV2.Current.Tests.QueryRuntime
open CanonicalPrefix TranscriptV2.Framing

private def first : Current.QueryRuntime.Packet Byte 1 where
  Data := Byte
  codec := PrefixCodec.byte
  role := .fingerprint
  cache _ := 0
  bounded value := by simp only [PrefixCodec.byte_encode,List.length_singleton]; omega

private def next : Current.QueryRuntime.Packet Byte 1 where
  Data := Byte
  codec := PrefixCodec.byte
  role := .sumcheck .binary 0 0
  cache value := value
  bounded value := by simp only [PrefixCodec.byte_encode,List.length_singleton]; omega

private def packets := [first,next]
private def blocks := packets.map Current.QueryRuntime.Packet.queryBlock
private def roles := packets.map Current.QueryRuntime.Packet.role
private def fits : 0+roles.length < 2^64 := by decide
private def link : Digest := fun _ => 3
private def value : Current.QueryCodec.Value PrefixCodec.byte blocks :=
  ((5 : Byte),.inr (link,((7 : Byte),.inl ())))
private abbrev Point := Input roles Byte (Current.QueryRuntime.Block 1 Byte) Digest Byte

private def pointMap (v : Current.QueryCodec.Value PrefixCodec.byte blocks) : Point :=
  Current.QueryRuntime.embed PrefixCodec.byte v.1 packets v

private def raw (point : Point) : Bytes :=
  Current.QueryRuntime.bytes PrefixCodec.byte roles 0 fits point

private theorem projection (v : Current.QueryCodec.Value PrefixCodec.byte blocks) :
    raw (pointMap v) = Current.QueryCodec.encode PrefixCodec.byte blocks 0 fits v :=
  Current.QueryRuntime.bytes_embed _ _ _ _ _ _

private def good : Point :=
  .round ⟨1,by decide⟩ ((5 : Byte),(⟨[5],by decide⟩,0),link) (⟨[7],by decide⟩,7)

example : pointMap value = good := rfl

private def wrongCache : Point :=
  .round ⟨1,by decide⟩ ((5 : Byte),(⟨[5],by decide⟩,0),link) (⟨[7],by decide⟩,99)

private def wrongContext : Point :=
  .round ⟨1,by decide⟩ ((6 : Byte),(⟨[5],by decide⟩,0),link) (⟨[7],by decide⟩,7)

example : raw wrongCache = raw good := rfl
example : raw wrongContext = raw good := rfl

private theorem unique_value (bad : Point) (hv : raw bad = raw good)
    (v : Current.QueryCodec.Value PrefixCodec.byte blocks) (h : pointMap v = bad) : v = value := by
  apply Current.QueryCodec.encode_injective PrefixCodec.byte blocks 0 fits
  rw [← projection,← projection,h,hv]
  rfl

-- The canonical image checks the reconstructed cache, rather than assuming
-- injection after arbitrary logical fields have been erased.
example : ¬ ∃ v, pointMap v = wrongCache := by
  rintro ⟨v,h⟩
  have he := unique_value wrongCache rfl v h
  subst v
  have hc := congrArg (fun point : Point => point.block.map Prod.snd) h
  change (some (7 : Byte)) = some 99 at hc
  exact (by decide : (some (7 : Byte)) ≠ some 99) hc

example : ¬ ∃ v, pointMap v = wrongContext := by
  rintro ⟨v,h⟩
  have he := unique_value wrongContext rfl v h
  subst v
  have hc := congrArg Input.context h
  change (5 : Byte) = 6 at hc
  exact (by decide : (5 : Byte) ≠ 6) hc

private def codec := Current.QueryCodec.intoCodec PrefixCodec.byte blocks 0 fits pointMap raw projection

example : codec.decode (raw good) = some ⟨good,⟨value,rfl⟩⟩ :=
  codec.decode_encode ⟨good,⟨value,rfl⟩⟩

end LfzkV2.Current.Tests.QueryRuntime
