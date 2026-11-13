import LfzkV2.Current.WireBlockRequest
import LfzkV2.Current.WireBlockBounds

/-! Transcript-operation vectors and rejection tests. In particular two
sumcheck scalars, one combine slice, u32 packing metadata and framed cell
counts have different wire shapes. -/
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
  adviceWrites := (PrefixCodec.vector PrefixCodec.byte 3).prefixed ([0] ++ TranscriptV2.Framing.encodeLE 8 3)
  adviceWritesWidth := 12
  adviceWritesLength value := by
    change (([0] ++ TranscriptV2.Framing.encodeLE 8 3) ++ (PrefixCodec.vector PrefixCodec.byte 3).encode value).length = 12
    rw [PrefixCodec.bytes_encode,List.length_append,List.length_ofFn]
    rfl

private def shape : Shape geometry fields where
  binaryPublic := 2
  primePublic := 2
  primeInputs := 3
  sharedBits := 2
  packingInputs := 2
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

-- Empty caller statements are valid. No coefficients or RHS appear here.
example : (packingStatement shape).encode (⟨[],by decide⟩,2,7) =
    frame (utf8 "longfellow/dual-packing128/trace-zero/v1") ++ frame [] ++ frame [2,0,0,0] ++
      frame (encodeLE 8 2) ++ frame (encodeLE 8 7) := by decide

-- The binary start binds the masked words, then the hash and fragment
-- statements, then the schedule with both circuit IDs and depths.
example (advice : Fin 3 → Byte) (hash fragment : CircuitStatement fields .binary 2)
    (circuits : CircuitSchedule 2) :
    (binaryStart repr shape).encode (advice,(hash,fragment),circuits) =
      (bytesDomain "p256-adapter/masked-quotient-bits/v1" ++ repr.adviceWrites.encode advice) ++
        (((statement repr shape .binary 2).encode hash ++ (statement repr shape .binary 2).encode fragment) ++
          (schedule 2).encode circuits) := rfl

example (circuits : CircuitSchedule 2) :
    (schedule 2).encode circuits =
      (bytesDomain "layered-sumcheck/circuits/v1" ++ frame (encodeLE 8 2)) ++
        (List.ofFn circuits).flatMap (framedDigest.pair word).encode := by
  change _ ++ (PrefixCodec.vector (framedDigest.pair word) 2).encode circuits = _
  rw [PrefixCodec.vector_encode]
  rfl

example (i : Fin geometry.roles.length) (value : Data (Advice := Fin 3 → Byte) shape i) :
    parse repr shape i ((codec repr shape i).encode value ++ [255]) = none := by
  simp only [parse,readWhole,(codec repr shape i).inverse,Option.bind_eq_bind,Option.bind_some]
  rfl

end LfzkV2.Current.Tests.WireBlocks
