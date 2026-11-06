import LfzkV2.Current.FrontendBody
import LfzkV2.Current.FrontendVerifier
import LfzkV2.Current.FrontendPrefix

/-! Body-facing frontend reconstruction. Successful parsing creates the
frontend, its compiled affine constraints and its replay together. The
message getter used by the transcript encoder is fixed to the same body
parser. Its zero totalization is used only outside successful branches;
no fallback certified application system is constructed. -/
noncomputable section
namespace LfzkV2.Current
open SumcheckV2

namespace FrontendBody
variable {F : Type} [Zero F]

/-- Malformed stage shapes still need a total public function for local
query counting. This contains only zero prover messages, never challenges,
pad values or an artificial certified circuit execution. -/
def zeroPayload : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.Payload circuit
  | _, _, .input => ()
  | _, _, .entry _ _ rest => zeroPayload rest
  | _, _, .layer _ _ rest => (⟨fun _ => ⟨0,0⟩,0,0,0⟩,zeroPayload rest)

variable {g : Geometry} {fields : Fields} {Advice Authentication : Type}

/-- The complete-proof message reader is fixed to its actual participant
body. An unsuccessful shape decode is totalized only for the encoder and
local analysis; `prepareBody` below rejects that branch. -/
def payloadOfBody {out input : ℕ} (side : Side) (field : fields side → F)
    (circuit : Layered.Circuit F out input)
    (proof : Replay.Output g fields Advice Authentication) : Layered.Replay.Payload circuit :=
  (ofBody circuit proof.body side field).getD (zeroPayload circuit)

theorem payloadOfBody_of_some {out input : ℕ} (side : Side) (field : fields side → F)
    (circuit : Layered.Circuit F out input) (proof : Replay.Output g fields Advice Authentication)
    (payload : Layered.Replay.Payload circuit)
    (h : ofBody circuit proof.body side field = some payload) :
    payloadOfBody side field circuit proof = payload := by
  simp only [payloadOfBody,h,Option.getD_some]

end FrontendBody

namespace FrontendVerifier.PrimeSetup
variable {N Slot Pad C : Type} [Field N] (setup : FrontendVerifier.PrimeSetup N Slot Pad)
variable {g : Geometry} {fields : Fields} {Advice Authentication : Type}

/-- Prime messages come from the actual prime body. On success both the
prepared frontend and its replay use this one decoded payload and answer tape. -/
def prepareBody (body : Body g fields Advice Authentication) (field : fields .prime → N)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (answers : ℕ → C) :
    Option (Σ prepared : Frontend.Prime N Slot Pad,
      Application.Replay prepared.circuit prepared.messages C) :=
  (FrontendBody.ofBody setup.circuit body .prime field).map fun payload =>
    ⟨setup.prepare payload decode nonzero answers,setup.replay payload decode nonzero answers⟩

/-- Parsing supplies the full prepared frontend/replay pair. This equality
is derived from the body reader; callers do not provide a message or compiler
correspondence certificate. -/
theorem prepareBody_decoded (body : Body g fields Advice Authentication) (field : fields .prime → N)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (answers : ℕ → C)
    (result : Σ prepared : Frontend.Prime N Slot Pad,
      Application.Replay prepared.circuit prepared.messages C)
    (h : setup.prepareBody body field decode nonzero answers = some result) :
    ∃ payload, FrontendBody.ofBody setup.circuit body .prime field = some payload ∧
      result = ⟨setup.prepare payload decode nonzero answers,setup.replay payload decode nonzero answers⟩ := by
  obtain ⟨payload,hpayload,he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨payload,hpayload,he.symm⟩

theorem prepareBody_exists_iff_shape (body : Body g fields Advice Authentication)
    (field : fields .prime → N) (decode : C → ℕ → N)
    (nonzero : C → Linear.TerminalSampling.Nonzero N) (answers : ℕ → C) :
    (∃ result, setup.prepareBody body field decode nonzero answers = some result) ↔
      g.prime.stages.map Stage.rounds = FrontendBody.widths setup.circuit := by
  constructor
  · rintro ⟨result,h⟩
    obtain ⟨payload,hpayload,_⟩ := setup.prepareBody_decoded body field decode nonzero answers result h
    exact (FrontendBody.decode_exists_iff_shape field setup.circuit g.prime body.prime).mp ⟨payload,hpayload⟩
  · intro hshape
    obtain ⟨payload,hpayload⟩ :=
      (FrontendBody.decode_exists_iff_shape field setup.circuit g.prime body.prime).mpr hshape
    exact ⟨⟨setup.prepare payload decode nonzero answers,setup.replay payload decode nonzero answers⟩,
      by simp only [prepareBody,FrontendBody.ofBody,hpayload,Option.map_some]⟩

end FrontendVerifier.PrimeSetup

namespace FrontendVerifier.PackedSetup
variable {B I J Slot Pad C : Type} [Field B] [Fintype B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J]
variable (setup : FrontendVerifier.PackedSetup B I J Slot Pad)
variable {g : Geometry} {fields : Fields} {Advice Authentication : Type}

/-- The packed frontend receives only its actual binary proof messages.
Packing response values remain separate protocol data, rather than new
field-valued inputs to the binary circuit. -/
def prepareBody (body : Body g fields Advice Authentication) (field : fields .binary → B)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (answers : ℕ → C) (U delta : I → B) (A : B) :
    Option (Σ prepared : Frontend.Packed B I J Slot Pad,
      Application.Replay prepared.circuit prepared.messages C) :=
  (FrontendBody.ofBody setup.circuit body .binary field).map fun payload =>
    ⟨setup.prepare payload decode nonzero answers U delta A,
      setup.replay payload decode nonzero answers U delta A⟩

theorem prepareBody_decoded (body : Body g fields Advice Authentication) (field : fields .binary → B)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (answers : ℕ → C) (U delta : I → B) (A : B)
    (result : Σ prepared : Frontend.Packed B I J Slot Pad,
      Application.Replay prepared.circuit prepared.messages C)
    (h : setup.prepareBody body field decode nonzero answers U delta A = some result) :
    ∃ payload, FrontendBody.ofBody setup.circuit body .binary field = some payload ∧
      result = ⟨setup.prepare payload decode nonzero answers U delta A,
        setup.replay payload decode nonzero answers U delta A⟩ := by
  obtain ⟨payload,hpayload,he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨payload,hpayload,he.symm⟩

theorem prepareBody_exists_iff_shape (body : Body g fields Advice Authentication)
    (field : fields .binary → B) (decode : C → ℕ → B)
    (nonzero : C → Linear.TerminalSampling.Nonzero B) (answers : ℕ → C)
    (U delta : I → B) (A : B) :
    (∃ result, setup.prepareBody body field decode nonzero answers U delta A = some result) ↔
      g.binary.stages.map Stage.rounds = FrontendBody.widths setup.circuit := by
  constructor
  · rintro ⟨result,h⟩
    obtain ⟨payload,hpayload,_⟩ := setup.prepareBody_decoded body field decode nonzero answers U delta A result h
    exact (FrontendBody.decode_exists_iff_shape field setup.circuit g.binary body.binary).mp ⟨payload,hpayload⟩
  · intro hshape
    obtain ⟨payload,hpayload⟩ :=
      (FrontendBody.decode_exists_iff_shape field setup.circuit g.binary body.binary).mpr hshape
    exact ⟨⟨setup.prepare payload decode nonzero answers U delta A,
      setup.replay payload decode nonzero answers U delta A⟩,
      by simp only [prepareBody,FrontendBody.ofBody,hpayload,Option.map_some]⟩

end FrontendVerifier.PackedSetup

namespace FrontendBody
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F : Type} [Field F]
variable {out input : ℕ}

/-- The typed frontend getter reconstructs the messages bound from the
actual body. The caller supplies public window bounds, not an arbitrary
payload reader or a semantic equality with the body. -/
theorem prefix_message
    (e : Replay.Encoding g fields Advice Authentication Key (Base × Layered.Replay.Message F) C)
    (side : Side) (field : fields side → F) (circuit : Layered.Circuit F out input) (start : ℕ)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Key (Base × Layered.Replay.Message F) → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (role : Layered.Replay.LayerRole circuit)
    (hbound : start+FrontendReplay.queryIndex circuit role 0 ≤ n) :
    Layered.Replay.layerMessage circuit
      (Replay.Encoding.frontendPayload circuit start
        (((e.withFrontend circuit (payloadOfBody side field circuit) start).chain initialLink).point proof H n)) role =
      Layered.Replay.layerMessage circuit (payloadOfBody side field circuit proof) role :=
  e.withFrontend_message circuit (payloadOfBody side field circuit) start initialLink proof H n hn hfit role hbound

/-- Successful shape decoding removes the zero totalization entirely. The
typed getter then exposes the same payload used to prepare the verifier's
messages, constraints and replay. -/
theorem prefix_message_of_some
    (e : Replay.Encoding g fields Advice Authentication Key (Base × Layered.Replay.Message F) C)
    (side : Side) (field : fields side → F) (circuit : Layered.Circuit F out input) (start : ℕ)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Key (Base × Layered.Replay.Message F) → Digest × C)
    (payload : Layered.Replay.Payload circuit)
    (hdecoded : ofBody circuit proof.body side field = some payload)
    (n : ℕ) (hn : n ≤ g.roles.length) (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (role : Layered.Replay.LayerRole circuit)
    (hbound : start+FrontendReplay.queryIndex circuit role 0 ≤ n) :
    Layered.Replay.layerMessage circuit
      (Replay.Encoding.frontendPayload circuit start
        (((e.withFrontend circuit (payloadOfBody side field circuit) start).chain initialLink).point proof H n)) role =
      Layered.Replay.layerMessage circuit payload role :=
  (prefix_message e side field circuit start initialLink proof H n hn hfit role hbound).trans
    (congrArg (fun p => Layered.Replay.layerMessage circuit p role)
      (payloadOfBody_of_some side field circuit proof payload hdecoded))

end FrontendBody
end LfzkV2.Current
