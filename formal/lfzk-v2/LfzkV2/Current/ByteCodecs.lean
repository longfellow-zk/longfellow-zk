import LfzkV2.Current.PrefixCodec
import TranscriptV2.FramingBounds

/-! Concrete finite byte representations used by the canonical-prefix model.
Bounds restrict the logical sample space; they do not add padding or bytes to
the runtime format. A successful parser must account for every consumed byte. -/
namespace LfzkV2.Current
open TranscriptV2.Framing (Byte encodeLE readLE readLE_encode_append readLE_sound take take_sound)

structure BoundedBytes (capacity : ℕ) where
  bytes : Bytes
  bound : bytes.length ≤ capacity

namespace BoundedBytes
variable {capacity : ℕ}

theorem ext {a b : BoundedBytes capacity} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- A length and exactly that many bytes give a finite presentation. No
unused tail is present in either the logical value or its serialization. -/
noncomputable instance : Fintype (BoundedBytes capacity) := by
  apply Fintype.ofInjective (fun value : BoundedBytes capacity =>
    (⟨⟨value.bytes.length,Nat.lt_succ_of_le value.bound⟩,fun i => value.bytes.get i⟩ :
      (length : Fin (capacity+1)) × (Fin length.val → Byte)))
  intro a b h
  apply ext
  have hv := congrArg (fun value : (length : Fin (capacity+1)) × (Fin length.val → Byte) =>
    List.ofFn value.2) h
  simpa only [List.ofFn_get] using hv

end BoundedBytes

namespace PrefixCodec
variable {A : Type}

/-- Restriction checks a canonical value after parsing, rather than silently
identifying several raw encodings with one typed value. -/
def restrict (codec : PrefixCodec A) (valid : A → Prop) [DecidablePred valid] :
    PrefixCodec {value // valid value} where
  encode value := codec.encode value.val
  decode bytes := do
    let (value,suffix) ← codec.decode bytes
    if h : valid value then some (⟨value,h⟩,suffix) else none
  inverse value suffix := by
    simp only [codec.inverse,Option.bind_eq_bind,Option.bind_some,dif_pos value.property]
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨decoded,rest⟩,hd,h⟩ := h
    split at h
    next hv =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      exact codec.canonical _ _ _ hd
    next hv => contradiction

/-- Fixed-width unsigned little-endian words, with the same range check
used for canonical field encodings and serialized count words. -/
def unsigned (width bound : ℕ) (fits : bound ≤ 256^width) : PrefixCodec (Fin bound) where
  encode value := encodeLE width value.val
  decode bytes := do
    let (value,suffix) ← readLE width bytes
    if h : value < bound then some (⟨value,h⟩,suffix) else none
  inverse value suffix := by
    rw [readLE_encode_append width value.val suffix (value.isLt.trans_le fits)]
    simp only [Option.bind_eq_bind,Option.bind_some,dif_pos value.isLt]
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨decoded,rest⟩,hd,h⟩ := h
    split at h
    next hv =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      exact (readLE_sound width bytes decoded rest hd).2
    next hv => contradiction

def byte : PrefixCodec Byte := unsigned 1 256 (by decide)

theorem byte_encode (value : Byte) : byte.encode value = [value] := by
  change [⟨value.val%256,Nat.mod_lt _ (by decide)⟩] = [value]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

private def emptyVector : Unit ≃ (Fin 0 → A) where
  toFun _ := Fin.elim0
  invFun _ := ()
  left_inv value := by cases value; rfl
  right_inv value := by funext i; exact Fin.elim0 i

private def vectorCons (length : ℕ) : (A × (Fin length → A)) ≃ (Fin (length+1) → A) where
  toFun value := Fin.cons value.1 value.2
  invFun value := (value 0,fun i => value i.succ)
  left_inv value := by cases value; rfl
  right_inv value := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Fixed geometry supplies vector counts. The bytes are consecutive values
in increasing physical index order, with no additional length word. -/
def vector (codec : PrefixCodec A) : (length : ℕ) → PrefixCodec (Fin length → A)
  | 0 => unit.equiv emptyVector
  | length+1 => (codec.pair (vector codec length)).equiv (vectorCons length)

theorem vector_encode (codec : PrefixCodec A) (length : ℕ) (value : Fin length → A) :
    (vector codec length).encode value = (List.ofFn value).flatMap codec.encode := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change codec.encode (value 0) ++ (vector codec length).encode (fun i => value i.succ) = _
      rw [ih,List.ofFn_succ,List.flatMap_cons]

theorem vector_length (codec : PrefixCodec A) (width : ℕ)
    (hlen : ∀ value, (codec.encode value).length = width) (count : ℕ)
    (value : Fin count → A) : ((PrefixCodec.vector codec count).encode value).length = count*width := by
  induction count with
  | zero => simp only [PrefixCodec.vector,PrefixCodec.equiv,PrefixCodec.unit,List.length_nil,Nat.zero_mul]
  | succ count ih =>
      change (codec.encode (value 0) ++
        (PrefixCodec.vector codec count).encode (fun i => value i.succ)).length = (count+1)*width
      rw [List.length_append,hlen,ih]
      ring

theorem bytes_encode (length : ℕ) (value : Fin length → Byte) :
    (vector byte length).encode value = List.ofFn value := by
  rw [vector_encode]
  rw [show byte.encode = (fun value => [value]) by funext value; exact byte_encode value,
    List.flatMap_singleton']

/-- Canonical scalar bytes in proof bodies have no transcript-operation tag. -/
def field (codec : TranscriptV2.Framing.FieldCodec A) : PrefixCodec A where
  encode := codec.encode
  decode := codec.read
  inverse := codec.read_encode_append
  canonical := codec.read_sound

private def emptyDependent (Element : Fin 0 → Type) : Unit ≃ ((i : Fin 0) → Element i) where
  toFun _ i := Fin.elim0 i
  invFun _ := ()
  left_inv value := by cases value; rfl
  right_inv value := by funext i; exact Fin.elim0 i

/-- Layers may have different public round counts. Their exact shapes are
part of the decoder, so the wire representation carries no redundant counts. -/
def dependentVector : (length : ℕ) → (Element : Fin length → Type) →
    (∀ i, PrefixCodec (Element i)) → PrefixCodec ((i : Fin length) → Element i)
  | 0, Element, _ => unit.equiv (emptyDependent Element)
  | length+1, Element, codecs =>
      ((codecs 0).pair (dependentVector length (fun i => Element i.succ) (fun i => codecs i.succ))).equiv
        (Fin.consEquiv Element)

/-- A canonical count word followed by exactly that many typed values. The
dependent payload records the actual count instead of filling a fixed tail. -/
def counted (width bound : ℕ) (fits : bound ≤ 256^width)
    (Element : Fin bound → Type) (codecs : ∀ i, PrefixCodec (Element i)) :
    PrefixCodec ((length : Fin bound) × Element length) where
  encode value := (unsigned width bound fits).encode value.1 ++ (codecs value.1).encode value.2
  decode bytes := do
    let (length,rest) ← (unsigned width bound fits).decode bytes
    let (value,suffix) ← (codecs length).decode rest
    some (⟨length,value⟩,suffix)
  inverse value suffix := by
    simp only [List.append_assoc,(unsigned width bound fits).inverse,
      Option.bind_eq_bind,Option.bind_some,(codecs value.1).inverse]
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨length,rest⟩,hl,⟨payload,last⟩,hp,heq⟩ := h
    cases Option.some.inj heq
    change (codecs length).decode rest = some (payload,last) at hp
    change bytes = ((unsigned width bound fits).encode length ++
      (codecs length).encode payload) ++ last
    rw [(unsigned width bound fits).canonical _ _ _ hl,(codecs length).canonical _ _ _ hp,
      List.append_assoc]

/-- A fixed marker is checked rather than retained as a freely variable
proof field. This adds exactly the existing marker bytes. -/
def marker (expected : Bytes) : PrefixCodec Unit where
  encode _ := expected
  decode bytes := do
    let (actual,suffix) ← take expected.length bytes
    if actual = expected then some ((),suffix) else none
  inverse value suffix := by
    cases value
    simp only [TranscriptV2.Framing.take_length_append,Option.bind_eq_bind,Option.bind_some]
    exact if_pos trivial
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨actual,rest⟩,ha,h⟩ := h
    split at h
    next he =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      change actual = expected at he
      rw [he] at ha
      exact (take_sound expected.length bytes expected rest ha).2
    next he => contradiction

def prefixed (codec : PrefixCodec A) (expected : Bytes) : PrefixCodec A :=
  ((marker expected).pair codec).equiv {
    toFun := Prod.snd
    invFun value := ((),value)
    left_inv value := by rcases value with ⟨⟨⟩,value⟩; rfl
    right_inv _ := rfl }

end PrefixCodec
end LfzkV2.Current
