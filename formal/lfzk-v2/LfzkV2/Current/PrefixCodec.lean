import TranscriptV2.FramingSound

/-! Prefix codecs for the existing transcript and complete proof formats.
Both inverse laws matter: encoding is injective, and a recognized byte string
has exactly one canonical encoding followed by its unconsumed suffix. -/
namespace LfzkV2.Current

abbrev Bytes := TranscriptV2.Framing.Bytes

structure PrefixCodec (A : Type) where
  encode : A → Bytes
  decode : Bytes → Option (A × Bytes)
  inverse : ∀ value suffix, decode (encode value ++ suffix) = some (value,suffix)
  canonical : ∀ bytes value suffix, decode bytes = some (value,suffix) → bytes = encode value ++ suffix

namespace PrefixCodec
variable {A B : Type} (first : PrefixCodec A)

theorem encode_injective : Function.Injective first.encode := by
  intro a b h
  have hi := congrArg first.decode (congrArg (· ++ []) h)
  simpa only [first.inverse,Option.some.injEq,Prod.mk.injEq,and_true] using hi

def unit : PrefixCodec Unit where
  encode _ := []
  decode bytes := some ((),bytes)
  inverse _ _ := rfl
  canonical bytes value suffix h := by
    obtain rfl := congrArg Prod.snd (Option.some.inj h)
    rfl

def pair (second : PrefixCodec B) : PrefixCodec (A × B) where
  encode value := first.encode value.1 ++ second.encode value.2
  decode bytes := do
    let (a,rest) ← first.decode bytes
    let (b,suffix) ← second.decode rest
    some ((a,b),suffix)
  inverse value suffix := by
    simp only [List.append_assoc,first.inverse,Option.bind_eq_bind,Option.bind_some,second.inverse]
  canonical bytes value suffix h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨a,rest⟩,ha,⟨b,last⟩,hb,heq⟩ := h
    cases Option.some.inj heq
    change second.decode rest = some (b,last) at hb
    change bytes = (first.encode a ++ second.encode b) ++ last
    rw [first.canonical _ _ _ ha,second.canonical _ _ _ hb,List.append_assoc]

def equiv (e : A ≃ B) : PrefixCodec B where
  encode value := first.encode (e.symm value)
  decode bytes := (first.decode bytes).map fun decoded => (e decoded.1,decoded.2)
  inverse value suffix := by simp only [first.inverse,Option.map_some,Equiv.apply_symm_apply]
  canonical bytes value suffix h := by
    obtain ⟨⟨a,rest⟩,ha,heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    simpa only [Equiv.symm_apply_apply] using first.canonical _ _ _ ha

/-- The valid-value subtype enforces the writer's u64 length restrictions.
The parser's soundness theorem supplies validity; no guessed size is accepted. -/
def schema {Index : Type} (Field : Index → Type)
    (codecs : ∀ i, TranscriptV2.Framing.FieldCodec (Field i))
    (shape : List (TranscriptV2.Framing.Kind Index)) :
    PrefixCodec {values : TranscriptV2.Framing.Values Field shape //
      TranscriptV2.Framing.ValidValues Field shape values} where
  encode values := TranscriptV2.Framing.encodeValues Field codecs shape values.val
  decode bytes := match h : TranscriptV2.Framing.decodeValues Field codecs shape bytes with
    | none => none
    | some (values,suffix) => some (⟨values,
        (TranscriptV2.Framing.decodeValues_sound Field codecs shape bytes values suffix h).1⟩,suffix)
  inverse value suffix := by
    have hi := TranscriptV2.Framing.decodeValues_encode_append Field codecs shape
      value.val suffix value.property
    split
    next h => rw [h] at hi; contradiction
    next values last h =>
      rw [h] at hi
      obtain ⟨hv,hs⟩ := Prod.mk.inj (Option.some.inj hi)
      subst values; subst last
      rfl
  canonical bytes value suffix h := by
    split at h
    next hd => contradiction
    next values rest hd =>
      obtain ⟨heq,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases heq
      exact (TranscriptV2.Framing.decodeValues_sound Field codecs shape bytes values rest hd).2

end PrefixCodec
end LfzkV2.Current
