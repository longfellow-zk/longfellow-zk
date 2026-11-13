import LfzkV2.Current.ConcreteMetadata

/-! The derived metadata and the verifier use the same recorded messages.
These equalities justify the total encoder defaults on successful parses;
they are conclusions of the existing partial reader, not extra certificates
supplied to an endpoint theorem. -/
noncomputable section
namespace LfzkV2.Current.ConcreteMetadata
open SumcheckV2 ApplicationSetup

variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
local notation "Point" => Input g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth)

namespace Prefix

def ofPoint (point : Point) (past : Fin point.rank → C) (fallback : C) :
    Prefix g fields Advice C point.rank where
  writes q := (point.readAt q.val (fun block => some block.2)).getD {}
  answers := past
  fallback := fallback

theorem ofPoint_fresh (point : Point) (past : Fin point.rank → C) (fallback : C) (q : ℕ) :
    (ofPoint point past fallback).fresh q = (point.readAt q (fun block => some block.2)).getD {} := by
  by_cases h : q < point.rank+1
  · simp only [fresh,dif_pos h,ofPoint]
  · have hn : ¬ q < point.rank := by omega
    have he : q ≠ point.rank := by omega
    simp only [fresh,dif_neg h,Input.readAt,Input.atRank,dif_neg hn,if_neg he,Option.bind_none,
      Option.getD_none]

theorem ofPoint_message {F : Type} (point : Point) (past : Fin point.rank → C) (fallback : C)
    (side : Side) (field : fields side → F) (start q : ℕ) :
    (ofPoint point past fallback).message side field start q =
      (ApplicationPrefix.wire point side field start q).getD .empty := by
  rw [message,ofPoint_fresh]
  unfold ApplicationPrefix.wire Input.readAt
  cases ((point.atRank (start+q)).bind Input.block) <;> rfl

theorem ofPoint_answer (point : Point) (past : Fin point.rank → C) (fallback : C) (q : ℕ) :
    (ofPoint point past fallback).answer q = (ApplicationPrefix.strictAnswer point past q).getD fallback := by
  unfold answer ofPoint ApplicationPrefix.strictAnswer
  split <;> rfl

theorem ofPoint_tape (point : Point) (past : Fin point.rank → C) (fallback : C) (start slots : ℕ) :
    (ofPoint point past fallback).tape start slots =
      ApplicationPrefix.frontendTape point past fallback start slots := by
  funext q
  change (if q < slots then (ofPoint point past fallback).answer (start+q) else fallback) = _
  rw [ofPoint_answer]
  rfl

end Prefix

variable {B : Type} [Field B]
variable {shared : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared) (samples : Samples B C) (primeField : fields .prime ≃ N)

/-- A successful ordinary prime reader reconstructs exactly the record
used for the rescaling metadata, including its split claim. -/
theorem primeData_readback (point : Point) (past : Fin point.rank → C) (data : PrimeData prime C)
    (read : ApplicationPrefix.readPrime prime primeField samples.prime samples.primeNonzero
      samples.fallback point past = some data) :
    primeData prime samples primeField (Prefix.ofPoint point past samples.fallback) = data := by
  obtain ⟨_,hp,hd,hn,ha⟩ := ApplicationPrefix.readPrime_spec prime primeField
    samples.prime samples.primeNonzero samples.fallback point past data read
  have hpayload : FrontendTranscript.read prime.circuit
      ((Prefix.ofPoint point past samples.fallback).message .prime primeField g.primeStart) = data.payload := by
    have hw : (Prefix.ofPoint point past samples.fallback).message .prime primeField g.primeStart =
        fun q => (ApplicationPrefix.wire point .prime primeField g.primeStart q).getD .empty := by
      funext q
      exact Prefix.ofPoint_message point past samples.fallback .prime primeField g.primeStart q
    rw [hw]
    exact ApplicationPrefix.Messages.readFrom_agrees prime.circuit _ 0 data.payload hp
  cases data with
  | mk payload decode nonzero answers =>
      dsimp only at hpayload hd hn ha
      subst decode
      subst nonzero
      subst answers
      subst payload
      have ht := Prefix.ofPoint_tape point past samples.fallback g.primeStart (FrontendReplay.slots prime.circuit)
      rw [← ht]
      rfl

end LfzkV2.Current.ConcreteMetadata
