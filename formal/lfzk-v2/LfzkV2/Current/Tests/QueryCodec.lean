import LfzkV2.Current.QueryCodec

/-! Literal framing checks and whole-input query cases. The small scalar
schema isolates the query grammar from the separately checked field codecs. -/
namespace LfzkV2.Current.Tests.QueryCodec
open CanonicalPrefix TranscriptV2.Framing

example : frame [5,6] = [0,2,0,0,0,0,0,0,0,5,6] := by decide
example : label .rowBatching = 11 := rfl
example : roundFooter .rowBatching 7 =
    frame roundDomain ++ frame [11] ++ frame [7,0,0,0,0,0,0,0] := by decide +kernel

private def scalar : PrefixCodec Byte := PrefixCodec.byte.prefixed [1]
private def blocks : List Current.QueryCodec.Block :=
  [⟨Byte,scalar,.sumcheck⟩,⟨Byte,scalar,.combine⟩]
private def fits : 0+blocks.length < 2^64 := by decide
private def firstLink : Digest := fun _ => 3
private def secondLink : Digest := fun _ => 4
private def first : Current.QueryCodec.Value PrefixCodec.byte blocks := (7,.inl ())
private def second : Current.QueryCodec.Value PrefixCodec.byte blocks := (7,.inr (firstLink,(8,.inl ())))
private def last : Current.QueryCodec.Value PrefixCodec.byte blocks :=
  (7,.inr (firstLink,(8,.inr (secondLink,⟨9,by decide⟩))))

private def firstBytes : Bytes := [1,7] ++ roundFooter .sumcheck 0
private def secondBytes : Bytes := firstBytes ++ feedback.encode firstLink ++ [1,8] ++ roundFooter .combine 1
private def finalBytes : Bytes := secondBytes ++ feedback.encode secondLink ++ finalFooter 2 ++ frame [9]

private theorem encode_first : Current.QueryCodec.encode PrefixCodec.byte blocks 0 fits first = firstBytes := by decide +kernel
private theorem encode_second : Current.QueryCodec.encode PrefixCodec.byte blocks 0 fits second = secondBytes := by decide +kernel
private theorem encode_final : Current.QueryCodec.encode PrefixCodec.byte blocks 0 fits last = finalBytes := by decide +kernel

example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits firstBytes = some first := by
  rw [← encode_first]
  exact Current.QueryCodec.decode_encode _ _ _ _ _
example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits secondBytes = some second := by
  rw [← encode_second]
  exact Current.QueryCodec.decode_encode _ _ _ _ _
example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits finalBytes = some last := by
  rw [← encode_final]
  exact Current.QueryCodec.decode_encode _ _ _ _ _

-- A suffix is a continuation only if it contains canonical link feedback.
example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits (firstBytes ++ [0]) = none := by decide +kernel
example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits
    ([1,7] ++ roundFooter .terminal 0) = none := by decide +kernel
example : Current.QueryCodec.decode PrefixCodec.byte blocks 0 fits
    ([1,7] ++ roundFooter .sumcheck 1) = none := by decide +kernel

-- Later schemas are not retroactively attached to an earlier query. This
-- sharing is required when public data becomes bound only in later blocks.
private def otherBlocks : List Current.QueryCodec.Block :=
  [⟨Byte,scalar,.sumcheck⟩,⟨Byte,scalar,.terminal⟩]
private def otherFits : 0+otherBlocks.length < 2^64 := by decide
private def otherFirst : Current.QueryCodec.Value PrefixCodec.byte otherBlocks := (7,.inl ())
example : Current.QueryCodec.encode PrefixCodec.byte blocks 0 fits first =
    Current.QueryCodec.encode PrefixCodec.byte otherBlocks 0 otherFits otherFirst := rfl

end LfzkV2.Current.Tests.QueryCodec
