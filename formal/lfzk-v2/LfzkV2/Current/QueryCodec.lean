import LfzkV2.Current.CanonicalPrefix
import LfzkV2.Current.ByteOracleTransport

/-! Whole-input parsing of an actual chained query. Ordinary round inputs
are prefixes of later inputs, so this is deliberately not a PrefixCodec for
the whole query. A parsed footer may end the query; otherwise actual link
feedback must precede the next role. Role-local schemas remain prefix codecs. -/
noncomputable section
namespace LfzkV2.Current.QueryCodec
open CanonicalPrefix
open scoped Classical

/-- One fixed role schema. Its data contains only writes bound at this
boundary; no later statement or other-field interpretation is encoded here. -/
structure Block where
  Data : Type
  codec : PrefixCodec Data
  domain : Domain

variable {Body : Type} (bodyCodec : PrefixCodec Body)

/-- A round may stop at its own query, or retain its actual answer link and
continue. After the last round only complete-body finalization is possible. -/
def Value : List Block → Type
  | [] => {body // (bodyCodec.encode body).length ≤ maxLength}
  | block :: tail => block.Data × (Unit ⊕ (Digest × Value tail))

private def after {A : Type} (codec : PrefixCodec A) (suffix : Bytes) : PrefixCodec A :=
  (codec.pair (PrefixCodec.marker suffix)).equiv {
    toFun := Prod.fst
    invFun value := (value,())
    left_inv value := by rcases value with ⟨value,⟨⟩⟩; rfl
    right_inv _ := rfl }

private def footer (block : Block) (counter : ℕ) (fits : counter < 2^64) : PrefixCodec block.Data :=
  after block.codec (roundFooter block.domain ⟨counter,fits⟩)

private def final (counter : ℕ) (fits : counter < 2^64) :
    PrefixCodec {body // (bodyCodec.encode body).length ≤ maxLength} :=
  (framed bodyCodec).prefixed (finalFooter ⟨counter,fits⟩)

/-- Every counter is checked against u64 before framing; the logical bound
adds no extra wire bytes. -/
def encode (bodyCodec : PrefixCodec Body) :
    (blocks : List Block) → (counter : ℕ) → counter+blocks.length < 2^64 → Value bodyCodec blocks → Bytes
  | [], counter, fits, body => (final bodyCodec counter fits).encode body
  | block :: tail, counter, fits, value =>
      (footer block counter (by simp only [List.length_cons] at fits; omega)).encode value.1 ++
        match value.2 with
        | .inl _ => []
        | .inr (link,next) => feedback.encode link ++
            encode bodyCodec tail (counter+1) (by simp only [List.length_cons] at fits; omega) next

/-- Exhaustion directly after a footer means that round's query. Otherwise
parse the mandatory feedback before advancing. The last branch consumes the
whole framed canonical body and rejects an ignored trailing suffix. -/
def decode (bodyCodec : PrefixCodec Body) :
    (blocks : List Block) → (counter : ℕ) → counter+blocks.length < 2^64 → Bytes → Option (Value bodyCodec blocks)
  | [], counter, fits, input => readWhole (final bodyCodec counter fits) input
  | block :: tail, counter, fits, input => do
      let (value,rest) ← (footer block counter (by simp only [List.length_cons] at fits; omega)).decode input
      if rest = [] then some (value,.inl ()) else do
        let (link,remaining) ← feedback.decode rest
        let next ← decode bodyCodec tail (counter+1)
          (by simp only [List.length_cons] at fits; omega) remaining
        some (value,.inr (link,next))

theorem encode_nil (counter : ℕ) (fits : counter+([] : List Block).length < 2^64)
    (body : Value bodyCodec []) :
    encode bodyCodec [] counter fits body =
      finalFooter ⟨counter,fits⟩ ++ frame (bodyCodec.encode body.val) := by
  simp only [encode,final,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,
    PrefixCodec.marker,Equiv.coe_fn_symm_mk,framed_encode]

theorem encode_stop (block : Block) (tail : List Block) (counter : ℕ)
    (fits : counter+(block::tail).length < 2^64) (value : block.Data) :
    encode bodyCodec (block::tail) counter fits (value,.inl ()) =
      block.codec.encode value ++
        roundFooter block.domain ⟨counter,by simp only [List.length_cons] at fits; omega⟩ := by
  simp only [encode,footer,after,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,List.append_nil]

theorem encode_continue (block : Block) (tail : List Block) (counter : ℕ)
    (fits : counter+(block::tail).length < 2^64) (value : block.Data)
    (link : Digest) (next : Value bodyCodec tail) :
    encode bodyCodec (block::tail) counter fits (value,.inr (link,next)) =
      block.codec.encode value ++
        roundFooter block.domain ⟨counter,by simp only [List.length_cons] at fits; omega⟩ ++
        feedback.encode link ++ encode bodyCodec tail (counter+1)
          (by simp only [List.length_cons] at fits; omega) next := by
  simp only [encode,footer,after,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,List.append_assoc]

/-- This is the actual parser/retraction law, proved from role-local
canonical parsing and mandatory link feedback. -/
theorem decode_encode (blocks : List Block) (counter : ℕ) (fits : counter+blocks.length < 2^64)
    (value : Value bodyCodec blocks) :
    decode bodyCodec blocks counter fits (encode bodyCodec blocks counter fits value) = some value := by
  induction blocks generalizing counter with
  | nil => exact readWhole_encode _ value
  | cons block tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop =>
          cases stop
          simp only [encode,List.append_nil,decode]
          have hi := (footer block counter (by simp only [List.length_cons] at fits; omega)).inverse value []
          simp only [List.append_nil] at hi
          simp only [hi,Option.bind_eq_bind,Option.bind_some,if_true]
      | inr continuation =>
          rcases continuation with ⟨link,next⟩
          simp only [encode,decode]
          rw [(footer block counter (by simp only [List.length_cons] at fits; omega)).inverse]
          simp only [Option.bind_eq_bind,Option.bind_some]
          rw [if_neg (by
            intro h
            exact feedback_nonempty link (List.append_eq_nil_iff.mp h).1),feedback.inverse]
          simp only [Option.bind_some,ih]

/-- Successful whole-input parsing accounts for every byte. In particular,
a final body or a different round cannot alias an earlier query prefix. -/
theorem encode_decode (blocks : List Block) (counter : ℕ) (fits : counter+blocks.length < 2^64)
    (input : Bytes) (value : Value bodyCodec blocks)
    (h : decode bodyCodec blocks counter fits input = some value) :
    encode bodyCodec blocks counter fits value = input := by
  induction blocks generalizing counter input with
  | nil => exact (readWhole_canonical _ _ _ h).symm
  | cons block tail ih =>
      simp only [decode,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨⟨current,rest⟩,hc,h⟩ := h
      split at h
      · rename_i hr
        cases Option.some.inj h
        have he := (footer block counter (by simp only [List.length_cons] at fits; omega)).canonical input current rest hc
        change rest = [] at hr
        simpa only [encode,hr,List.append_nil] using he.symm
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨⟨link,remaining⟩,hl,next,hn,heq⟩ := h
        cases Option.some.inj heq
        simp only [encode]
        rw [ih _ _ _ _ hn]
        rw [← feedback.canonical rest link remaining hl]
        exact ((footer block counter (by simp only [List.length_cons] at fits; omega)).canonical input current rest hc).symm

theorem encode_injective (blocks : List Block) (counter : ℕ) (fits : counter+blocks.length < 2^64) :
    Function.Injective (encode bodyCodec blocks counter fits) := by
  intro first second h
  have hd := congrArg (decode bodyCodec blocks counter fits) h
  rw [decode_encode,decode_encode] at hd
  exact Option.some.inj hd

/-- The whole codec supplies exactly the retraction needed by byte-oracle
transport. Its validity predicate is true because Value already records the
role schema, canonical fields, bounded body and exact continuation shape. -/
def codec (blocks : List Block) (counter : ℕ) (fits : counter+blocks.length < 2^64) :
    ByteOracleTransport.Codec (Value bodyCodec blocks) Bytes (fun _ => True) where
  encode value := encode bodyCodec blocks counter fits value.val
  decode input := (decode bodyCodec blocks counter fits input).map fun value => ⟨value,trivial⟩
  decode_encode value := by simp only [decode_encode,Option.map_some]
  encode_decode input value h := by
    obtain ⟨decoded,hd,heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    exact encode_decode bodyCodec blocks counter fits input decoded hd


/-- A parsed physical prefix can carry a redundant typed cache. Agreement
of its byte projection suffices to prove cache injection on canonical values. -/
theorem pointMap_injective {Point : Type} (blocks : List Block) (counter : ℕ)
    (fits : counter+blocks.length < 2^64) (pointMap : Value bodyCodec blocks → Point)
    (pointBytes : Point → Bytes)
    (hbytes : ∀ value, pointBytes (pointMap value) = encode bodyCodec blocks counter fits value) :
    Function.Injective pointMap := by
  intro first second h
  apply encode_injective bodyCodec blocks counter fits
  rw [← hbytes first,← hbytes second,h]

/-- Canonical typed points are exactly the parsed physical-prefix image.
The whole-input parser reconstructs the cache; its inverse is derived from
component codecs and the byte projection, with no all-input injectivity
premise for arbitrary malformed caches. -/
def intoCodec {Point : Type} (blocks : List Block) (counter : ℕ)
    (fits : counter+blocks.length < 2^64) (pointMap : Value bodyCodec blocks → Point)
    (pointBytes : Point → Bytes)
    (hbytes : ∀ value, pointBytes (pointMap value) = encode bodyCodec blocks counter fits value) :
    ByteOracleTransport.Codec Point Bytes (fun point => ∃ value, pointMap value = point) where
  encode point := pointBytes point.val
  decode input := (decode bodyCodec blocks counter fits input).map fun value =>
    ⟨pointMap value,⟨value,rfl⟩⟩
  decode_encode point := by
    rcases point with ⟨point,⟨value,rfl⟩⟩
    rw [hbytes,decode_encode]
    rfl
  encode_decode input point h := by
    obtain ⟨value,hvalue,heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    rw [hbytes]
    exact encode_decode bodyCodec blocks counter fits input value hvalue

end LfzkV2.Current.QueryCodec
