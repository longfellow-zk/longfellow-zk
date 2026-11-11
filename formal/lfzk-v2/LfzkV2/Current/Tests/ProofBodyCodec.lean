import LfzkV2.Current.ProofBodyReplay
import LfzkV2.Current.ProofBodyBounds
import LfzkV2.Current.ProofOutput

/-! Literal MDA6/JPG2 ordering and rejection checks. Distinct byte-valued
coordinates make field order, layer order and row-major openings visible. -/
namespace LfzkV2.Current.Tests.ProofBodyCodec
open TranscriptV2.Framing (Byte FieldCodec)

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
  binary := ⟨[⟨[],[],2⟩],[]⟩
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

private def repr : Current.ProofBodyCodec.Representations fields (Fin 3 → Byte) where
  binary := rawField 16 (by decide) (by decide)
  prime := rawField 32 (by decide) (by decide)
  binaryWidth := rfl
  primeWidth := rfl
  advice := PrefixCodec.vector PrefixCodec.byte 3
  adviceWidth := 3
  adviceLength value := by rw [PrefixCodec.bytes_encode,List.length_ofFn]

private def byte (value : ℕ) : Byte := ⟨value%256,Nat.mod_lt _ (by decide)⟩

private def body : Body geometry fields (Fin 3 → Byte) (OpeningBody.Authentication geometry) where
  commitment := fun _ => 1
  fingerprints := ((fun _ => 7,fun _ => 8),(fun _ => 9,fun _ => 10))
  mu := fun _ => 11
  advice := ![90,91,12]
  binary _ := {
    coefficients := fun i => (fun _ => byte (12+2*i.val),fun _ => byte (13+2*i.val))
    cross := fun _ => 16
    claims := (fun _ => 17,fun _ => 18) }
  prime _ := {
    coefficients := fun _ => (fun _ => 22,fun _ => 23)
    cross := fun _ => 24
    claims := (fun _ => 25,fun _ => 26) }
  packing := (fun i _ => byte (19+i.val),fun _ => 21)
  binaryBackend := {
    response := {
      h := fun i _ => byte (30+i.val)
      z := fun i _ => byte (34+i.val) }
    rows := fun i j _ => byte (40+2*i.val+j.val) }
  primeBackend := {
    response := {
      h := fun i _ => byte (60+i.val)
      z := fun i _ => byte (64+i.val) }
    rows := fun i j _ => byte (70+2*i.val+j.val) }
  authentication := {
    context := fun _ => 2
    nonce := fun i _ => byte (3+i.val)
    frontierLength := ⟨2,by decide⟩
    frontier := fun i _ => byte (5+i.val) }

private def blocks (width : ℕ) (values : List Byte) : Bytes :=
  values.flatMap (List.replicate width)

private def wire : Bytes :=
  [77,68,65,54] ++ List.replicate 32 1 ++ blocks 16 [7,8] ++ blocks 32 [9,10,11] ++ [90,91,12] ++
    blocks 16 [12,13,14,15,16,17,18] ++ blocks 16 [19,20,21] ++ blocks 32 [22,23,24,25,26] ++
    [74,80,71,50] ++ List.replicate 32 2 ++
    blocks 16 [30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] ++
    blocks 32 [60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79] ++
    List.replicate merkleNonceBytes 3 ++ List.replicate merkleNonceBytes 4 ++
    [2,0,0,0] ++ List.replicate 32 5 ++ List.replicate 32 6

private theorem encode_wire : (Current.ProofBodyCodec.codec repr geometry).encode body = wire := by decide +kernel

-- The full body has no final seal and no implicit padding.
example : wire.length = 1615 := by decide +kernel

-- The public maximum allows the full frontier, without changing actual
-- serialization. It also discharges final framing uniformly for all bodies.
example : ProofBodyBounds.bodyBound repr geometry = 1807 := by decide +kernel
example : ((Current.ProofBodyCodec.codec repr geometry).encode body).length ≤
    CanonicalPrefix.maxLength :=
  ProofBodyBounds.final_fits repr geometry (by decide +kernel) body

-- Canonical parsing retains a following seal or a concatenated outer suffix.
example : (Current.ProofBodyCodec.codec repr geometry).decode (wire ++ [99,100]) = some (body,[99,100]) := by
  rw [← encode_wire]
  exact (Current.ProofBodyCodec.codec repr geometry).inverse body [99,100]

private def proof : Proof geometry fields (Fin 3 → Byte) (OpeningBody.Authentication geometry) :=
  ⟨body,fun _ => 88⟩

-- Complete-proof encoding appends the seal without placing it in the body.
private theorem complete_wire : (ProofBodyReplay.complete repr geometry).encode proof = wire ++ List.replicate 32 88 := by
  rw [ProofBodyReplay.complete_encode]
  dsimp only [proof]
  rw [encode_wire]
  rfl

example : ProofOutput.read repr (wire ++ List.replicate 32 88) = some proof := by
  rw [← complete_wire]
  exact ProofOutput.read_encode repr proof

-- A successful parse replaces even an unrelated fallback seal.
example : ProofOutput.decode repr {proof with finalSeal := fun _ => 99}
    ((),wire ++ List.replicate 32 88) = ⟨(),proof⟩ := by
  apply ProofOutput.decode_of_read
  rw [← complete_wire]
  exact ProofOutput.read_encode repr proof

example : (ProofBodyReplay.complete repr geometry).decode (wire ++ List.replicate 32 88 ++ [99]) =
    some (proof,[99]) := by
  have he : (ProofBodyReplay.complete repr geometry).encode proof = wire ++ List.replicate 32 88 := by
    rw [ProofBodyReplay.complete_encode]
    dsimp only [proof]
    rw [encode_wire]
    rfl
  rw [← he]
  exact (ProofBodyReplay.complete repr geometry).inverse proof [99]

example : ProofOutput.read (g := geometry) repr (wire ++ List.replicate 32 88 ++ [99]) = none := by
  have hd : (ProofBodyReplay.complete repr geometry).decode (wire ++ List.replicate 32 88 ++ [99]) =
      some (proof,[99]) := by
    rw [← complete_wire]
    exact (ProofBodyReplay.complete repr geometry).inverse proof [99]
  unfold ProofOutput.read CanonicalPrefix.readWhole
  rw [hd]
  rfl

-- A mismatched public joint context is rejected by the checked body codec.
example : (Current.ProofBodyCodec.checked repr geometry (fun _ => 3)).decode wire = none := by
  have hs : (Current.ProofBodyCodec.codec repr geometry).decode wire = some (body,[]) := by
    rw [← encode_wire]
    simpa only [List.append_nil] using (Current.ProofBodyCodec.codec repr geometry).inverse body []
  have hn : body.authentication.context ≠ (fun _ => 3) := by
    intro h
    have he := congrFun h 0
    exact (by decide : (2 : Byte) ≠ 3) he
  simp only [Current.ProofBodyCodec.checked,PrefixCodec.restrict,hs,
    Option.bind_eq_bind,Option.bind_some,dif_neg hn]

-- The fixed MDA6 marker rejects a wrong version immediately.
example : (Current.ProofBodyCodec.codec repr geometry).decode [77,68,65,53] = none := rfl

-- Degree-one packing is exactly empty, including its decoder's suffix.
example : (Current.ProofBodyCodec.packing PrefixCodec.byte 1).encode () = [] := rfl
example : (Current.ProofBodyCodec.packing PrefixCodec.byte 1).decode [8,9] = some ((),[8,9]) := rfl

-- A counted frontier rejects truncation and a count above its public cap.
example : (Current.ProofBodyCodec.frontier geometry).decode [1,0,0,0,7] = none := by decide
example : (Current.ProofBodyCodec.frontier geometry).decode [9,0,0,0] = none := by decide

end LfzkV2.Current.Tests.ProofBodyCodec
