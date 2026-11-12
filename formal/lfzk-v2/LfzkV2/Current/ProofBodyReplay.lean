import LfzkV2.Current.ProofBodyCodec

/-! Complete-proof bytes keep the final seal separate from its hashed body.
At final replay, the body bytes are derived from the actual proof, including
its one authentication frontier. No caller-chosen final buffer is involved. -/
namespace LfzkV2.Current.ProofBodyReplay

variable {g : Geometry} {fields : Fields} {Advice Context Block C : Type}

private def proofData (g : Geometry) (fields : Fields) (Advice : Type) :
    (Body g fields Advice (OpeningBody.Authentication g) × Digest) ≃
      Proof g fields Advice (OpeningBody.Authentication g) where
  toFun value := ⟨value.1,value.2⟩
  invFun value := (value.body,value.finalSeal)
  left_inv _ := rfl
  right_inv value := by cases value; rfl

/-- The body is followed by precisely its 32-byte seal. The body codec
itself is the independently proved MDA6/JPG2 canonical codec. -/
def complete (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) :
    PrefixCodec (Proof g fields Advice (OpeningBody.Authentication g)) :=
  ((ProofBodyCodec.codec repr g).pair ProofBodyCodec.digest).equiv (proofData g fields Advice)

theorem complete_encode (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry)
    (proof : Proof g fields Advice (OpeningBody.Authentication g)) :
    (complete repr g).encode proof = (ProofBodyCodec.codec repr g).encode proof.body ++ List.ofFn proof.finalSeal := by
  simp only [complete,PrefixCodec.equiv,PrefixCodec.pair,proofData,Equiv.coe_fn_symm_mk,
    ProofBodyCodec.digest,PrefixCodec.bytes_encode]

theorem complete_length (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry)
    (proof : Proof g fields Advice (OpeningBody.Authentication g)) :
    ((complete repr g).encode proof).length = ((ProofBodyCodec.codec repr g).encode proof.body).length+32 := by
  rw [complete_encode,List.length_append,List.length_ofFn]

/-- Ordinary boundary inputs contain no complete body. The final-seal
constructor is the sole source of these canonical body bytes. -/
def finalBodyBytes (repr : ProofBodyCodec.Representations fields Advice) :
    Replay.Point g fields Advice (OpeningBody.Authentication g) Context Block → Option Bytes
  | .round .. => none
  | .finalSeal _ body => some ((ProofBodyCodec.codec repr g).encode body)

/-- Final replay binds the actual complete canonical body, including the
terminal authentication data and excluding the seal being checked. -/
theorem finalBodyBytes_replay (repr : ProofBodyCodec.Representations fields Advice)
    (e : Replay.Encoding g fields Advice (OpeningBody.Authentication g) Context Block C)
    (initialLink : Digest) (proof : Proof g fields Advice (OpeningBody.Authentication g))
    (H : Replay.Point g fields Advice (OpeningBody.Authentication g) Context Block → Digest × C) :
    finalBodyBytes repr ((e.chain initialLink).finalSealPoint proof H) =
      some ((ProofBodyCodec.codec repr g).encode proof.body) := by
  obtain ⟨history,hpoint⟩ := e.finalSealPoint_body initialLink proof H
  rw [hpoint]
  rfl

/-- Changing the body's semantic value changes its canonical bytes. This
is derived from the component parsers rather than assumed for finalization. -/
theorem body_bytes_injective (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) :
    Function.Injective (ProofBodyCodec.codec repr g).encode :=
  (ProofBodyCodec.codec repr g).encode_injective

end LfzkV2.Current.ProofBodyReplay
