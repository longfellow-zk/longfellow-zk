import LfzkV2.Current.WireBlocks

/-! Structural capacities for complete round blocks. Bounds depend on public
counts and representation widths, never on enumerating possible field values.
They size the finite oracle-query type and do not serialize any padding. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open scoped Classical
open CanonicalPrefix

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (shape : Shape g fields)

instance startDataFintype (start : Start) : Fintype (StartData (Advice := Advice) shape start) := by
  cases start <;> simp only [StartData,PrimeStart,BinaryStart,CircuitStatement,CircuitSchedule] <;> infer_instance

instance packingHeaderFintype : Fintype (PackingHeader shape) := by
  unfold PackingHeader
  split <;> infer_instance

instance packingStatementFintype : Fintype (PackingStatement shape) := inferInstance

instance packingAFintype : Fintype (PackingA g fields) := by
  unfold PackingA
  split <;> infer_instance

instance roleDataFintype (role : Role) : Fintype (RoleData shape role) := by
  cases role <;> simp only [RoleData,SourceStatement] <;> infer_instance

instance dataFintype (i : Fin g.roles.length) : Fintype (Data (Advice := Advice) shape i) := inferInstance

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
/-- Both header profiles have at most two framed byte payloads. The basis ID
is a fixed four-byte payload in the binary profile. -/
def packingHeaderBound : ℕ :=
  if shape.binary128Packing then
    (bytesDomain "longfellow/dual-packing128/trace-zero/v1").length+9+maxLength+13
  else (bytesDomain "longfellow/dual-packing/generic/trace-zero/v1").length+2*(9+maxLength)

section Sizes
variable (repr : ProofBodyCodec.Representations fields Advice)
omit [∀ side, Fintype (fields side)] [Fintype Advice]

private theorem word_length (value : Word) : (word.encode value).length = 17 := by
  rw [word_encode,frame_length,TranscriptV2.Framing.encodeLE_length]

private theorem scalar_length {F : Type} (field : TranscriptV2.Framing.FieldCodec F) (value : F) :
    ((scalar field).encode value).length = 1+field.width := by
  rw [scalar_encode,List.length_append,field.length]
  rfl

private theorem slice_length {F : Type} (field : TranscriptV2.Framing.FieldCodec F)
    (count : ℕ) (value : Fin count → F) :
    ((slice field count).encode value).length = 9+count*field.width := by
  change (([2] ++ TranscriptV2.Framing.encodeLE 8 count) ++
    (PrefixCodec.vector (PrefixCodec.field field) count).encode value).length = _
  rw [List.length_append,PrefixCodec.vector_length _ field.width field.length]
  simp only [List.length_append,List.length_singleton,TranscriptV2.Framing.encodeLE_length]

private theorem pairSlice_length {F : Type} (field : TranscriptV2.Framing.FieldCodec F) (value : F × F) :
    ((pairSlice field).encode value).length = 9+2*field.width := by
  change (([2] ++ TranscriptV2.Framing.encodeLE 8 2) ++
    (field.encode value.1 ++ field.encode value.2)).length = _
  simp only [List.length_append,List.length_singleton,TranscriptV2.Framing.encodeLE_length,field.length]
  omega

private theorem field_width_le (side : Side) : (fieldCodec repr side).width ≤ 32 := by
  cases side <;> simp only [fieldCodec,repr.binaryWidth,repr.primeWidth] <;> omega

private theorem statement_length (side : Side) (count : ℕ) (value : CircuitStatement fields side count) :
    ((statement repr shape side count).encode value).length = 41+(count+1)*(1+(fieldCodec repr side).width) := by
  rw [statement,followed_encode]
  change ((framedDigest.encode value.1 ++
    (PrefixCodec.vector (scalar (fieldCodec repr side)) count).encode value.2) ++
    ([1] ++ (fieldCodec repr side).encode (shape.zero side))).length = _
  simp only [List.length_append,framedDigest_length,
    PrefixCodec.vector_length _ _ (scalar_length (fieldCodec repr side)),
    (fieldCodec repr side).length,List.length_singleton]
  ring

private theorem schedule_length (count : ℕ) (value : CircuitSchedule count) :
    ((schedule count).encode value).length =
      (bytesDomain "layered-sumcheck/circuits/v1").length+17+58*count := by
  change ((bytesDomain "layered-sumcheck/circuits/v1" ++ frame (TranscriptV2.Framing.encodeLE 8 count)) ++
    (PrefixCodec.vector (framedDigest.pair word) count).encode value).length = _
  rw [List.length_append,PrefixCodec.vector_length _ 58 (by
    intro v
    change (framedDigest.encode v.1 ++ word.encode v.2).length = _
    rw [List.length_append,framedDigest_length,word_length])]
  simp only [List.length_append,frame_length,TranscriptV2.Framing.encodeLE_length]
  omega

/-- A start block carries either fingerprint responses and one prime circuit,
or the masked quotient words, two binary statements and a two-circuit schedule. Summing their lengths
bounds either case without inspecting any message value. -/
def startBound : ℕ :=
  (bytesDomain "longfellow/witness-selection/responses/v1").length+41+73+
    (41+(shape.primePublic+1)*33)+
    ((bytesDomain "layered-sumcheck/circuits/v1").length+17+58) +
  ((bytesDomain "p256-adapter/masked-quotient-bits/v1").length+repr.adviceWritesWidth+
    2*(41+(shape.binaryPublic+1)*17)+
    ((bytesDomain "layered-sumcheck/circuits/v1").length+17+116))

private theorem start_length_le (start : Start) (value : StartData (Advice := Advice) shape start) :
    ((startCodec repr shape start).encode value).length ≤ startBound shape repr := by
  cases start with
  | none => exact Nat.zero_le _
  | prime =>
    change ((bytesDomain "longfellow/witness-selection/responses/v1") ++
      (((pairSlice repr.binary).encode value.1.1 ++ (pairSlice repr.prime).encode value.1.2) ++
      ((statement repr shape .prime shape.primePublic).encode value.2.1 ++
      (schedule 1).encode value.2.2))).length ≤ _
    simp only [List.length_append,pairSlice_length,statement_length,schedule_length,
      fieldCodec,repr.binaryWidth,repr.primeWidth]
    unfold startBound
    omega
  | binary =>
    change ((bytesDomain "p256-adapter/masked-quotient-bits/v1" ++ repr.adviceWrites.encode value.1) ++
      (((statement repr shape .binary shape.binaryPublic).encode value.2.1.1 ++
        (statement repr shape .binary shape.binaryPublic).encode value.2.1.2) ++
      (schedule 2).encode value.2.2)).length ≤ _
    simp only [List.length_append,repr.adviceWritesLength,statement_length,schedule_length,
      fieldCodec,repr.binaryWidth]
    unfold startBound
    omega

private theorem cast_length_le {A B : Type} (h : A = B) (codec : PrefixCodec A) (bound : ℕ)
    (hlen : ∀ value, (codec.encode value).length ≤ bound) (value : B) :
    ((cast (congrArg PrefixCodec h) codec).encode value).length ≤ bound := by
  cases h
  exact hlen value

private theorem packingHeader_length_le (value : PackingHeader shape) :
    ((packingHeader shape).encode value).length ≤ packingHeaderBound shape := by
  by_cases h : shape.binary128Packing
  · simp only [packingHeader,packingHeaderBound,h,↓reduceDIte,↓reduceIte]
    exact cast_length_le (by simp only [PackingHeader,h,↓reduceIte]) _ _ (by
      intro v
      change ((bytesDomain "longfellow/dual-packing128/trace-zero/v1") ++
        (bytes.encode v ++ frame (TranscriptV2.Framing.encodeLE 4 2))).length ≤ _
      simp only [List.length_append,bytes_length,frame_length,TranscriptV2.Framing.encodeLE_length]
      have hv := v.bound
      omega) value
  · simp only [packingHeader,packingHeaderBound,h,Bool.false_eq_true,↓reduceDIte,↓reduceIte]
    exact cast_length_le (by simp only [PackingHeader,h,Bool.false_eq_true,↓reduceIte]) _ _ (by
      intro v
      change ((bytesDomain "longfellow/dual-packing/generic/trace-zero/v1") ++
        (bytes.encode v.1 ++ bytes.encode v.2)).length ≤ _
      simp only [List.length_append,bytes_length]
      have h₁ := v.1.bound
      have h₂ := v.2.bound
      omega) value

private theorem packingA_length_le (value : PackingA g fields) :
    ((packingA repr shape).encode value).length ≤
      (bytesDomain (if shape.binary128Packing then "trace-zero128/A" else "trace-zero/A")).length+17 := by
  by_cases h : g.packingDegree = 1
  · simp only [packingA,h,↓reduceDIte]
    exact cast_length_le (by simp only [PackingA,h,↓reduceIte]) _ _ (by
      intro v
      exact Nat.zero_le _) value
  · simp only [packingA,h,↓reduceDIte]
    exact cast_length_le (by simp only [PackingA,h,↓reduceIte]) _ _ (by
      intro v
      change ((bytesDomain (if shape.binary128Packing then "trace-zero128/A" else "trace-zero/A")) ++
        (scalar repr.binary).encode v).length ≤ _
      rw [List.length_append,scalar_length,repr.binaryWidth]) value

private theorem response_length (side : Side) (value : Response g (fields side)) :
    ((response repr side).encode value).length =
      18+(3*g.rowDimension+g.maskingDegree)*(fieldCodec repr side).width := by
  change ((slice (fieldCodec repr side) (g.rowDimension+g.maskingDegree)).encode value.h ++
    (slice (fieldCodec repr side) (2*g.rowDimension)).encode value.z).length = _
  rw [List.length_append,slice_length,slice_length]
  ring

/-- Sum of the public sizes of the possible role packets. The largest small
packet is a two-element slice: a tag and u64 count plus two 32-byte
scalars. The remaining terms account for larger slices and domain markers. This need not be a tight bound:
only actual canonical bytes are ever written or accepted. -/
def roleBound : ℕ :=
  (9+2*32) +
  (bytesDomain "native-masked-sumcheck/all-linear-rows/v1").length+(bytesDomain "all-linear-rows").length +
  (bytesDomain "native-shared-prefix/nonzero-rescaling/v2").length +
  ((bytesDomain "native-shared-prefix/masked-opening/v2").length+
    33+(bytesDomain "p256-adapter/two-independent-full-field-rescalings/v3").length) +
  (packingHeaderBound shape+34+(9+16*g.packingDegree)) +
  ((bytesDomain (if shape.binary128Packing then "trace-zero128/A" else "trace-zero/A")).length+17+198) +
  (36+(3*g.rowDimension+g.maskingDegree)*48)

private theorem role_length_le (role : Role) (value : RoleData shape role) :
    ((roleCodec repr shape role).encode value).length ≤ roleBound shape := by
  cases role with
  | fingerprint => exact Nat.zero_le _
  | inputAssertions | assertions =>
    rw [roleCodec,word_length]
    unfold roleBound
    omega
  | sumcheck side _ _ =>
    change ((scalar (fieldCodec repr side)).encode value.1 ++
      (scalar (fieldCodec repr side)).encode value.2).length ≤ _
    simp only [List.length_append,scalar_length]
    have h := field_width_le repr side
    unfold roleBound
    omega
  | terminal side _ =>
    change ((scalar (fieldCodec repr side)).encode value).length ≤ _
    rw [scalar_length]
    have h := field_width_le repr side
    unfold roleBound
    omega
  | combine side _ =>
    change ((pairSlice (fieldCodec repr side)).encode value).length ≤ _
    rw [pairSlice_length]
    have h := field_width_le repr side
    unfold roleBound
    omega
  | rowBatching =>
    change (bytesDomain "native-masked-sumcheck/all-linear-rows/v1" ++ bytesDomain "all-linear-rows").length ≤ _
    rw [List.length_append]
    unfold roleBound
    omega
  | rescaling =>
    change (bytesDomain "native-shared-prefix/nonzero-rescaling/v2").length ≤ _
    unfold roleBound
    omega
  | conversion =>
    rw [roleCodec,followed_encode]
    change ((bytesDomain "native-shared-prefix/masked-opening/v2" ++ (scalar repr.prime).encode value) ++
      bytesDomain "p256-adapter/two-independent-full-field-rescalings/v3").length ≤ _
    simp only [List.length_append,scalar_length,repr.primeWidth]
    unfold roleBound
    omega
  | packing =>
    change (((packingHeader shape).encode value.1.1 ++
      (word.encode value.1.2.1 ++ word.encode value.1.2.2)) ++
      (slice repr.binary g.packingDegree).encode value.2).length ≤ _
    simp only [List.length_append,word_length,slice_length,repr.binaryWidth]
    have h := packingHeader_length_le shape value.1.1
    unfold roleBound
    omega
  | batching =>
    change ((packingA repr shape).encode value.1 ++
      (sourceStatement.encode value.2.1 ++ sourceStatement.encode value.2.2)).length ≤ _
    have hs (s : SourceStatement) : (sourceStatement.encode s).length = 99 := by
      change (framedDigest.encode s.1 ++ (framedDigest.encode s.2.1 ++ word.encode s.2.2)).length = _
      simp only [List.length_append,framedDigest_length,word_length]
    simp only [List.length_append,hs]
    have h := packingA_length_le shape repr value.1
    unfold roleBound
    omega
  | opening =>
    change ((response repr .binary).encode value.1 ++ (response repr .prime).encode value.2).length ≤ _
    simp only [List.length_append,response_length,fieldCodec,repr.binaryWidth,repr.primeWidth]
    unfold roleBound
    omega

/-- A structural bound on complete ordinary blocks. Only public dimensions
and fixed codec widths occur in the type; no field-valued packet is enumerated. -/
def blockBound : ℕ := startBound shape repr+roleBound shape

theorem encode_length_le (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    ((codec repr shape i).encode value).length ≤ blockBound shape repr := by
  change ((startCodec repr shape (startAt g i)).encode value.1 ++
    (roleCodec repr shape (g.roles.get i)).encode value.2).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (start_length_le shape repr _ value.1) (role_length_le shape repr _ value.2)

/-- The bounded base retains the complete encoded block. Its type is finite
without treating an unbounded byte list as an oracle-query coordinate. -/
def bounded (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    BoundedBytes (blockBound shape repr) :=
  ⟨(codec repr shape i).encode value,encode_length_le shape repr i value⟩

@[simp] theorem bounded_bytes (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    (bounded shape repr i value).bytes = (codec repr shape i).encode value := rfl

end Sizes
end LfzkV2.Current.WireBlocks
