import LfzkV2.Current.WireBlockRequest
import LfzkV2.Current.WireBlockBounds

/-! Transcript-operation vectors and rejection tests. In particular two
sumcheck scalars, one combine slice, u32 packing metadata and a framed RHS
term count have different wire shapes. -/
namespace LfzkV2.Current.Tests.WireBlocks
open TranscriptV2.Framing (Byte FieldCodec encodeLE)
open Current.WireBlocks CanonicalPrefix

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

private def fields : Fields
  | .binary => Fin 16 → Byte
  | .prime => Fin 32 → Byte

private def geometry : Geometry where
  binary := ⟨[⟨[],[],1⟩],[]⟩
  prime := ⟨[⟨[],[],1⟩],[]⟩
  binaryCells := 0
  primeCells := 0
  packingDegree := 2
  packingPositive := by decide
  rowDimension := 3
  maskingDegree := 1
  columns := 8
  openings := 2
  openingsPositive := by decide
  openings_lt := by decide
  openings_le := by decide
  responseFits := by decide
  productFits := by decide

private def repr : ProofBodyCodec.Representations fields (Fin 3 → Byte) where
  binary := rawField 16 (by decide) (by decide)
  prime := rawField 32 (by decide) (by decide)
  binaryWidth := rfl
  primeWidth := rfl
  advice := PrefixCodec.vector PrefixCodec.byte 3
  adviceWidth := 3
  adviceLength value := by rw [PrefixCodec.bytes_encode,List.length_ofFn]

private def shape : Shape geometry fields where
  binaryPublic := 2
  primePublic := 2
  primeInputs := 3
  sharedBits := 2
  packingWeights := 2
  packingTermBound := 4
  packingTermFits := by decide
  binary128Packing := true
  zero side := match side with | .binary => fun _ => 0 | .prime => fun _ => 0
  sliceFits := by decide

private def b (value : Byte) : fields .binary := fun _ => value

example : (word.encode 4660) = [0,8,0,0,0,0,0,0,0,52,18,0,0,0,0,0,0] := by decide

example : (roleCodec repr shape (.sumcheck .binary 0 0)).encode (b 7,b 9) =
    [1] ++ List.replicate 16 7 ++ [1] ++ List.replicate 16 9 := by decide

example : (roleCodec repr shape (.combine .binary 0 [])).encode (b 7,b 9) =
    [2,2,0,0,0,0,0,0,0] ++ List.replicate 16 7 ++ List.replicate 16 9 := by decide

example : (roleCodec repr shape (.combine .binary 0 [])).decode
    ([2,3,0,0,0,0,0,0,0] ++ List.replicate 32 7) = none := by decide

example : (roleCodec repr shape .rowBatching).encode () =
    frame (utf8 "native-masked-sumcheck/all-linear-rows/v1") ++ frame (utf8 "all-linear-rows") := rfl

example : (packingHeader shape).encode ⟨[17,19],by decide⟩ =
    frame (utf8 "longfellow/dual-packing128/trace-zero/v1") ++
      frame [17,19] ++ frame [2,0,0,0] := by decide

example : (packingTerms repr shape).encode ⟨⟨1,by decide⟩,fun _ => (7,b 9)⟩ =
    frame (encodeLE 8 1) ++ frame (encodeLE 8 7) ++ [1] ++ List.replicate 16 9 := by decide

example (i : Fin geometry.roles.length) (value : Data (Advice := Fin 3 → Byte) shape i) :
    parse repr shape i ((codec repr shape i).encode value ++ [255]) = none := by
  simp only [parse,readWhole,(codec repr shape i).inverse,Option.bind_eq_bind,Option.bind_some]
  rfl

end LfzkV2.Current.Tests.WireBlocks
