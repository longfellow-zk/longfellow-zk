import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ApplicationPrefix
import LfzkV2.Current.MetadataIdentifiers

/-! Bind-only writes reconstructed from the actual causal history. Prover
messages remain the responsibility of `WireBlocks.fromRequest`. This module
chooses the runtime's computations for the intervening affine claims and
statement identifiers; a caller no longer chooses a function of the whole
history that happens to have the right type.

Unavailable messages and answers have fixed defaults solely to make the
encoder total on malformed prefixes. The ordinary application decoder still
rejects missing messages; no accepted branch is manufactured by those defaults.
-/
noncomputable section
namespace LfzkV2.Current.ConcreteMetadata
open SumcheckV2 ApplicationSetup
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}

/-- Only the current message and strict earlier answers are available. -/
structure Prefix (g : Geometry) (fields : Fields) (Advice C : Type) (index : ℕ) where
  writes : Fin (index+1) → ProtocolWrites.Fresh g fields Advice
  answers : Fin index → C
  fallback : C

namespace Prefix
variable {index : ℕ} (history : Prefix g fields Advice C index)

def fresh (q : ℕ) : ProtocolWrites.Fresh g fields Advice :=
  if h : q < index+1 then history.writes ⟨q,h⟩ else {}

def answer (q : ℕ) : C :=
  if h : q < index then history.answers ⟨q,h⟩ else history.fallback

def message {F : Type} (side : Side) (field : fields side → F) (start q : ℕ) :
    Layered.Replay.Message F :=
  ApplicationPrefix.mapMessage field ((history.fresh (start+q)).frontend side)

def tape (start slots q : ℕ) : C :=
  if q < slots then history.answer (start+q) else history.fallback

@[simp] theorem answer_past (q : Fin index) : history.answer q.val = history.answers q := by
  simp only [answer,dif_pos q.isLt]

@[simp] theorem answer_current : history.answer index = history.fallback := by
  simp only [answer,lt_self_iff_false,↓reduceDIte]

@[simp] theorem fresh_present (q : Fin (index+1)) : history.fresh q.val = history.writes q := by
  simp only [fresh,dif_pos q.isLt]

end Prefix

variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder

/-- Sampler operations have the same role as the ideal sampler interface in
the endpoint theorem. In particular both conversion coordinates read one answer. -/
structure Samples (B C : Type) [Field B] where
  binary : C → ℕ → B
  binaryNonzero : C → Linear.TerminalSampling.Nonzero B
  prime : C → ℕ → N
  primeNonzero : C → Linear.TerminalSampling.Nonzero N
  conversion : C → Fin 2 → Linear.TerminalSampling.Nonzero N
  fallback : C

variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (shape : WireBlocks.Shape g fields)

/-- Public size facts and static identifiers. None is a function of proof
messages. The only auxiliary function hashes an already constructed byte string.
The main hash circuit depth is trusted circuit-description data, just like its ID. -/
structure Public where
  binaryCount : shape.binaryPublic = binary.nPublic
  primeCount : shape.primePublic = prime.nPublic
  primeInputs : shape.primeInputs = shared+prime.remaining+prime.pads
  sharedBits : shape.sharedBits = shared
  packingInputs : shape.packingInputs = binary.nPrivate
  binary128 : shape.binary128Packing = true
  binaryPadsFit : binary.pads < 2^64
  primeDepthFit : prime.circuit.layers < 2^64
  adapterDepthFit : (MetadataIdentifiers.reductions (F := B) binary.shape).length+2 < 2^64
  binaryRowsFit : g.affineRows .binary < 2^64
  primeRowsFit : g.affineRows .prime < 2^64
  hashDepth : WireBlocks.Word
  binaryContext : Digest
  primeContext : Digest
  identifierHash : Bytes → Digest

variable (samples : Samples B C)
variable (primeField : fields .prime ≃ N)

def primeData {index : ℕ} (history : Prefix g fields Advice C index) : PrimeData prime C :=
  let payload := FrontendTranscript.read prime.circuit (history.message .prime primeField g.primeStart)
  let answers := history.tape g.primeStart (FrontendReplay.slots prime.circuit)
  { payload := payload
    decode := samples.prime
    nonzero := samples.primeNonzero
    answers := answers
    rho := fun i => samples.prime (history.answer (ApplicationPrefix.rowBatchingIndex g)) i.val }

/-- Dense order is all private prime inputs, followed by the sumcheck pads.
Dedicated fingerprint masks have no coordinate in this transmitted claim. -/
def primeWeights (data : PrimeData prime C) : Fin (shared+prime.remaining+prime.pads) → N :=
  Fin.append
    (fun i => Sum.elim data.claim.sharedWeights data.claim.otherWeights
      (CellLayout.Prime.input shared prime.remaining prime.pads i))
    (fun i => data.claim.otherWeights (CellLayout.Prime.pad prime.remaining prime.pads i))

def conversionWeights (data : PrimeData prime C) (eta : N) : Fin (shared+1) → N :=
  Fin.append (fun i => eta*data.claim.sharedWeights i) (fun _ => 1)

def rescaling {index : ℕ} (history : Prefix g fields Advice C index) : N :=
  (samples.primeNonzero (history.answer (ApplicationPrefix.rescalingIndex g))).val

def powers {index : ℕ} (generator : Bˣ) (data : PrimeData prime C)
    (history : Prefix g fields Advice C index) : Fin 2 → Fin (shared+maskBits) → Bˣ :=
  fun tree i => generator^((samples.conversion
    (history.answer (ApplicationPrefix.conversionIndex g)) tree).val *
      Handoff.weights data.claim.sharedWeights (rescaling samples history) i).val

def targets {index : ℕ} (generator : Bˣ) (history : Prefix g fields Advice C index) : Fin 2 → Bˣ :=
  let mu := primeField ((history.fresh (ApplicationPrefix.conversionIndex g)).mu.getD (primeField.symm 0))
  fun tree => generator^((samples.conversion (history.answer (ApplicationPrefix.conversionIndex g)) tree).val*mu).val

def masked {index : ℕ} (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (history : Prefix g fields Advice C index) : Fin 2 → Fin adviceBits → Bool :=
  (((history.fresh g.binaryStart).advice).bind advice).getD (fun _ _ => false)

private def digestBytes (value : Digest) : BoundedBytes CanonicalPrefix.maxLength :=
  ⟨List.ofFn value,by simp [CanonicalPrefix.maxLength]⟩

variable (params : Public binary prime shape)

/-- Public values change no size, source ID or frontend address. -/
def Public.withInputs (binaryInputs : Fin binary.nPublic → Bool) (primeInputs : Fin prime.nPublic → N) :
    Public { binary with publicBits := binaryInputs } { prime with publicInputs := primeInputs } shape :=
  ⟨params.binaryCount,params.primeCount,params.primeInputs,params.sharedBits,params.packingInputs,
    params.binary128,params.binaryPadsFit,params.primeDepthFit,
    params.adapterDepthFit,params.binaryRowsFit,params.primeRowsFit,params.hashDepth,
    params.binaryContext,params.primeContext,params.identifierHash⟩

/-- Packing identifies the already-derived source, retaining only its public
cell counts in the byte transcript. The complete affine expression remains a
local computation of the verifier, as in the Polygero statement interface. -/
def packingStatement (sourceId : Digest) : WireBlocks.PackingStatement shape := by
  let header : WireBlocks.PackingHeader shape := by
    simpa only [WireBlocks.PackingHeader,params.binary128,↓reduceIte] using digestBytes sourceId
  have inputsFit : binary.nPrivate < 2^64 := by
    rw [← params.packingInputs]
    exact shape.sliceFits _ (by simp)
  exact (header,⟨binary.nPrivate,inputsFit⟩,⟨binary.pads,params.binaryPadsFit⟩)

/-- LFC3 source coordinates use the unpadded shared input array. The
algebraic circuit subsequently embeds those same coordinates into its cube. -/
def adapterSources : Fin (shared+maskBits) → ℕ :=
  Fin.append (fun i => binary.nPublic+(binary.sharedPrivate i).val)
    (fun i => binary.nPublic+(binary.maskPrivate i).val)

def adapterPads : Fin 2 → Fin adviceBits → ℕ :=
  fun tree i => binary.nPublic+(binary.advicePrivate tree i).val

def adapterId {index : ℕ} (encode : B → Bytes) (generator : Bˣ) (data : PrimeData prime C)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (history : Prefix g fields Advice C index) : Digest :=
  MetadataIdentifiers.adapterId params.identifierHash encode binary.shape
    (binary.nPublic+binary.nPrivate) binary.nPublic (adapterSources binary) (adapterPads binary)
    (powers prime samples generator data history) (generator^(-(Adapter.Mdoc.primeOrder : ℤ)))
    (masked advice history) (targets samples primeField generator history)

def start {index : ℕ} (ids : FingerprintPrefix.Setup) (encode : B → Bytes) (generator : Bˣ)
    (data : PrimeData prime C) (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (history : Prefix g fields Advice C index) :
    (stage : WireBlocks.Start) → WireBlocks.StartMetadata shape stage
  | .none => ()
  | .prime => ((ids.primeCircuit,fun _ => shape.zero .prime),
      fun _ => (ids.primeCircuit,⟨prime.circuit.layers,params.primeDepthFit⟩))
  | .binary =>
      let generated := adapterId binary prime shape samples primeField params encode generator data advice history
      ((ids.hashCircuit,fun _ => shape.zero .binary),
        (generated,fun _ => shape.zero .binary),
        Fin.cons (ids.hashCircuit,params.hashDepth)
          (Fin.cons (generated,⟨(MetadataIdentifiers.reductions (F := B) binary.shape).length+2,
            params.adapterDepthFit⟩) Fin.elim0))

def role {index : ℕ} (ids : FingerprintPrefix.Setup)
    (data : PrimeData prime C)
    (history : Prefix g fields Advice C index) :
    (stage : Role) → WireBlocks.RoleMetadata shape stage
  | .rescaling => (fun i => primeField.symm (primeWeights prime data (Fin.cast params.primeInputs i)),
      primeField.symm data.claim.target)
  | .conversion => fun i => primeField.symm
      (conversionWeights prime data (rescaling samples history) (Fin.cast (congrArg (·+1) params.sharedBits) i))
  | .packing => packingStatement binary prime shape params ids.hashCircuit
  | .batching => ((ids.hashCircuit,params.binaryContext,⟨g.affineRows .binary,params.binaryRowsFit⟩),
      (ids.primeCircuit,params.primeContext,⟨g.affineRows .prime,params.primeRowsFit⟩))
  | .fingerprint | .inputAssertions .. | .assertions .. | .sumcheck .. |
      .terminal .. | .combine .. | .rowBatching | .opening => ()

/-- Instantiate the causal wire encoder. Both frontend compilers use the
request's public values. Prime coefficients use the earlier messages and answers;
packing writes only its statement identifier and public layout. -/
def metadata (ids : FingerprintPrefix.Setup) (encode : B → Bytes) (generator : Bˣ)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool)) :
    CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic :=
  fun request index writes past =>
    let binary' : BinaryPublic B shared maskBits adviceBits := { binary with publicBits := request.publicBits }
    let prime' : PrimePublic N shared :=
      { prime with publicInputs := fun i => primeField (request.primeInputs (Fin.cast params.primeCount.symm i)) }
    let params' : Public binary' prime' shape := params.withInputs binary prime shape request.publicBits prime'.publicInputs
    let history : Prefix g fields Advice C index.val := ⟨writes,past,samples.fallback⟩
    let data := primeData prime' samples primeField history
    (start binary' prime' shape samples primeField params' ids encode generator data advice history
        (WireBlocks.startAt g index),
      role binary' prime' shape samples primeField params' ids data history
        (g.roles.get index))

end LfzkV2.Current.ConcreteMetadata
