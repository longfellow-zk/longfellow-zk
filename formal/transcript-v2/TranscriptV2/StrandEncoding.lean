import TranscriptV2.FramingSound

/-! Exact SHA-256 preimages used by the Rust strand implementation. The hash
itself remains an oracle; finalization means ordinary padded SHA-256, not an
exposed compression state. Type tags, strand ids, parent counts and PRF counters
are raw words, not transcript write frames. Both node and PRF inputs bind the
strand id, independently of the digest values. -/
namespace TranscriptV2.Strand
open Framing

abbrev Digest := Fin 32 → Byte
abbrev Word := Fin (2^64)

def digestCodec : FieldCodec Digest where
  width := 32
  positive := by decide
  buffer := by decide
  encode := List.ofFn
  decode bytes := if h : bytes.length = 32 then
    some (fun i => bytes.get ⟨i.val,by rw [h]; exact i.isLt⟩) else none
  length _ := List.length_ofFn
  inverse value := by
    split
    next h =>
      congr 1
      funext i
      simp only [List.get_eq_getElem,List.getElem_ofFn]
    next h => exact (h (List.length_ofFn)).elim
  canonical payload value h := by
    split at h
    next hp =>
      cases Option.some.inj h
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using hp.symm
      · intro i hi hj
        simp only [List.getElem_ofFn,List.get_eq_getElem]
    next hp => contradiction

def word (value : Word) : Bytes := encodeLE 8 value.val

def readWord (bytes : Bytes) : Option (Word × Bytes) := do
  let (value,rest) ← readLE 8 bytes
  if h : value < 2^64 then some (⟨value,h⟩,rest) else none

theorem readWord_encode_append (value : Word) (suffix : Bytes) :
    readWord (word value ++ suffix) = some (value,suffix) := by
  have h : value.val < 256^8 := by simpa only [show 256^8 = 2^64 by norm_num] using value.isLt
  simp only [readWord,word,readLE_encode_append 8 value.val suffix h,
    Option.bind_eq_bind,Option.bind_some,dif_pos value.isLt]

theorem readWord_sound (bytes : Bytes) (value : Word) (suffix : Bytes)
    (h : readWord bytes = some (value,suffix)) : bytes = word value ++ suffix := by
  simp only [readWord,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨decoded,rest⟩,hd,h⟩ := h
  split at h
  next hv =>
    cases Option.some.inj h
    exact (readLE_sound 8 bytes decoded rest hd).2
  next hv => contradiction

inductive Input where
  | prf (id : Word) (parent : Digest) (counter : Word)
  | root (message : Bytes)
  | node (id : Word) (parents : List Digest) (message : Bytes)

def Input.id : Input → Word
  | .prf id .. => id
  | .root _ => 0
  | .node id .. => id

def Input.Valid : Input → Prop
  | .node _ parents .. => parents ≠ [] ∧ parents.length < 2^32
  | _ => True

def Input.encode : Input → Bytes
  | .prf id parent counter => encodeLE 4 0 ++ word id ++ List.ofFn parent ++ word counter
  | .root message => encodeLE 4 1 ++ word 0 ++ encodeLE 4 0 ++ message
  | .node id parents message => encodeLE 4 1 ++ word id ++ encodeLE 4 parents.length ++
      digestCodec.encodeSlice parents ++ message

/-- Arbitrary SHA inputs are permitted, but only canonical inputs belong to
the strand/PRF domains. A PRF query has no ignored suffix. A root has id zero.
Multi-parent encodings can occur in adversarial oracle queries, but the runtime
constructs only zero-parent roots and one-parent continuations. -/
def Input.decode (bytes : Bytes) : Option Input := do
  let (tag,rest) ← readLE 4 bytes
  let (id,rest) ← readWord rest
  if tag = 0 then
    let (parent,rest) ← digestCodec.read rest
    let (counter,rest) ← readWord rest
    if rest = [] then some (.prf id parent counter) else none
  else if tag = 1 then
    let (count,rest) ← readLE 4 rest
    let (parents,rest) ← digestCodec.readSlice count rest
    if count = 0 then
      if id = 0 then some (.root rest) else none
    else some (.node id parents rest)
  else none

theorem Input.decode_encode (input : Input) (valid : input.Valid) :
    Input.decode input.encode = some input := by
  have hzero : 0 < 256^4 := by decide
  have hone : 1 < 256^4 := by decide
  cases input with
  | prf id parent counter =>
      have hw := readWord_encode_append counter []
      simp only [List.append_nil] at hw
      simp only [Input.encode,List.append_assoc,Input.decode,
        readLE_encode_append 4 0 _ hzero,readWord_encode_append,
        Option.bind_eq_bind,Option.bind_some,↓reduceIte,
        show List.ofFn parent = digestCodec.encode parent from rfl,
        digestCodec.read_encode_append,hw]
  | root message =>
      simp only [Input.encode,List.append_assoc,Input.decode,
        readLE_encode_append 4 1 _ hone,readWord_encode_append,
        readLE_encode_append 4 0 _ hzero,
        Option.bind_eq_bind,Option.bind_some,show ¬(1:ℕ)=0 by decide,↓reduceIte,
        FieldCodec.readSlice]
  | node id parents message =>
      have hn : parents.length ≠ 0 := by
        intro h
        exact valid.1 (List.length_eq_zero_iff.mp h)
      have hb : parents.length < 256^4 := by
        simpa only [show 256^4 = 2^32 by norm_num] using valid.2
      simp only [Input.encode,List.append_assoc,Input.decode,
        readLE_encode_append 4 1 _ hone,readWord_encode_append,
        readLE_encode_append 4 parents.length _ hb,
        Option.bind_eq_bind,Option.bind_some,show ¬(1:ℕ)=0 by decide,↓reduceIte,
        digestCodec.readSlice_encode_append,hn]

theorem Input.encode_injective {a b : Input} (ha : a.Valid) (hb : b.Valid)
    (h : a.encode = b.encode) : a = b := by
  have hd := congrArg Input.decode h
  rw [Input.decode_encode a ha,Input.decode_encode b hb] at hd
  exact Option.some.inj hd

/-- Position separation is a byte-syntax fact, independent of oracle outputs. -/
theorem Input.encode_ne_of_id_ne {a b : Input} (ha : a.Valid) (hb : b.Valid)
    (different : a.id ≠ b.id) : a.encode ≠ b.encode :=
  fun same => different (congrArg Input.id (Input.encode_injective ha hb same))

/-- Successful decoding accounts for every byte and enforces the parent
count. Arbitrary auxiliary SHA inputs cannot create aliases of valid nodes. -/
theorem Input.decode_sound (bytes : Bytes) (input : Input)
    (h : Input.decode bytes = some input) : input.Valid ∧ bytes = input.encode := by
  simp only [Input.decode,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨tag,afterTag⟩,htag,⟨⟨id,rest⟩,hid,h⟩⟩ := h
  split at h
  next hz =>
    change tag = 0 at hz
    subst tag
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨parent,remaining⟩,hp,⟨⟨counter,suffix⟩,hc,h⟩⟩ := h
    split at h
    next he =>
      change suffix = [] at he
      cases Option.some.inj h
      refine ⟨trivial,?_⟩
      rw [(readLE_sound 4 bytes 0 afterTag htag).2,
        readWord_sound afterTag id rest hid,
        digestCodec.read_sound rest parent remaining hp,
        readWord_sound remaining counter suffix hc,he]
      rfl
    next he => contradiction
  next hz =>
    split at h
    next ho =>
      change tag = 1 at ho
      subst tag
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨count,remaining⟩,hc,⟨⟨parents,afterParents⟩,hp,h⟩⟩ := h
      obtain ⟨hbound,hcount⟩ := readLE_sound 4 rest count remaining hc
      obtain ⟨hlen,hparents⟩ := digestCodec.readSlice_sound count remaining parents afterParents hp
      split at h
      next he =>
        change count = 0 at he
        split at h
        next hi =>
          change id = 0 at hi
          cases Option.some.inj h
          have hp0 : parents = [] := List.length_eq_zero_iff.mp (hlen.trans he)
          refine ⟨trivial,?_⟩
          rw [(readLE_sound 4 bytes 1 afterTag htag).2,
            readWord_sound afterTag id rest hid,hi,hcount,he,hparents,hp0]
          rfl
        next hi => contradiction
      next he =>
        change count ≠ 0 at he
        cases Option.some.inj h
        refine ⟨⟨?_,?_⟩,?_⟩
        · intro hempty
          apply he
          change parents = [] at hempty
          rw [hempty,List.length_nil] at hlen
          exact hlen.symm
        · rw [hlen]
          simpa only [show 256^4 = 2^32 by norm_num] using hbound
        · rw [(readLE_sound 4 bytes 1 afterTag htag).2,
            readWord_sound afterTag id rest hid,hcount,hparents]
          simp only [Input.encode,hlen,List.append_assoc]
    next ho => contradiction

theorem Input.prf_ne_root (id : Word) (parent : Digest) (counter : Word) (message : Bytes) :
    (Input.prf id parent counter).encode ≠ (Input.root message).encode := by
  intro h
  have hh := congrArg List.head? h
  change some (0 : Byte) = some 1 at hh
  norm_num at hh

theorem Input.prf_ne_node (prfId : Word) (parent : Digest) (counter : Word)
    (nodeId : Word) (parents : List Digest) (message : Bytes) :
    (Input.prf prfId parent counter).encode ≠ (Input.node nodeId parents message).encode := by
  intro h
  have hh := congrArg List.head? h
  change some (0 : Byte) = some 1 at hh
  norm_num at hh

@[simp] theorem Input.prf_length (id : Word) (parent : Digest) (counter : Word) :
    (Input.prf id parent counter).encode.length = 52 := by
  simp [Input.encode,word]

@[simp] theorem Input.root_length (message : Bytes) :
    (Input.root message).encode.length = 16+message.length := by
  simp only [Input.encode,word,List.length_append,encodeLE_length]

@[simp] theorem Input.node_length (id : Word) (parents : List Digest) (message : Bytes) :
    (Input.node id parents message).encode.length = 16+32*parents.length+message.length := by
  simp only [Input.encode,word,List.length_append,encodeLE_length,
    FieldCodec.encodeSlice_length,digestCodec]
  omega

end TranscriptV2.Strand
