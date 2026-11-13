import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ApplicationPrefix
import LfzkV2.Current.MetadataIdentifiers

/-! Fixed bind-only metadata for the current verifier. Actual prover
messages and request public inputs are assigned by `WireBlocks.fromRequest`.
Derived affine claims and the adapter's virtual definitions remain local and
cannot enter the metadata constructor. Prefix helpers support the separate
application readback proofs; they are not used to serialize metadata. -/
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

/-- Public size facts and static identifiers. None depends on proof messages
or oracle challenges. The hash depth is trusted circuit-description data. -/
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

variable (samples : Samples B C)
variable (primeField : fields .prime ≃ N)

def primeData {index : ℕ} (history : Prefix g fields Advice C index) : PrimeData prime C :=
  let payload := FrontendTranscript.read prime.circuit (history.message .prime primeField g.primeStart)
  let answers := history.tape g.primeStart (FrontendReplay.slots prime.circuit)
  { payload := payload
    decode := samples.prime
    nonzero := samples.primeNonzero
    answers := answers }

private def digestBytes (value : Digest) : BoundedBytes CanonicalPrefix.maxLength :=
  ⟨List.ofFn value,by simp [CanonicalPrefix.maxLength]⟩

variable (params : Public binary prime shape)

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

/-- Metadata contains only fixed public identifiers, depths and counts.
No oracle answer or challenge-derived coefficient can enter these packets. -/
def start (ids : FingerprintPrefix.Setup) :
    (stage : WireBlocks.Start) → WireBlocks.StartMetadata shape stage
  | .none => ()
  | .prime => ((ids.primeCircuit,fun _ => shape.zero .prime),
      fun _ => (ids.primeCircuit,⟨prime.circuit.layers,params.primeDepthFit⟩))
  | .binary => (((ids.hashCircuit,fun _ => shape.zero .binary),(ids.fragment,fun _ => shape.zero .binary)),
      Fin.cons (ids.hashCircuit,params.hashDepth)
        (Fin.cons (ids.fragment,⟨(MetadataIdentifiers.reductions (F := B) binary.shape).length+2,
          params.adapterDepthFit⟩) Fin.elim0))

def role (ids : FingerprintPrefix.Setup) :
    (stage : Role) → WireBlocks.RoleMetadata shape stage
  | .packing => packingStatement binary prime shape params ids.hashCircuit
  | .batching => ((ids.hashCircuit,params.binaryContext,⟨g.affineRows .binary,params.binaryRowsFit⟩),
      (ids.primeCircuit,params.primeContext,⟨g.affineRows .prime,params.primeRowsFit⟩))
  | .fingerprint | .inputAssertions .. | .assertions .. | .sumcheck .. |
      .terminal .. | .combine .. | .rowBatching | .rescaling | .conversion | .opening => ()

/-- Fixed public metadata plus actual body messages are the only absorbed
values. Request public inputs are installed separately by `fromRequest`.
The history and challenge arguments of the general replay interface are
intentionally ignored, rather than reconstructed and then reabsorbed. -/
def metadata (ids : FingerprintPrefix.Setup) :
    CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic :=
  fun _ index _ _ =>
    (start binary prime shape params ids (WireBlocks.startAt g index),
      role binary prime shape params ids (g.roles.get index))

omit [Fintype B] [DecidableEq B] in
/-- The concrete mdoc transcript satisfies the global absorption invariant:
its metadata is a function of the block index alone. It absorbs no request
value beyond the statement, no prover message beyond the body's own fields,
and no value derived from prover messages or challenges. This holds for
arbitrary message prefixes and answer arrays, including adversarial ones. -/
theorem metadata_setupOnly (ids : FingerprintPrefix.Setup) :
    CanonicalRequest.SetupOnly shape binary.nPublic
      (metadata (Advice := Advice) (C := C) binary prime shape params ids) := by
  intro request request' index writes writes' first second
  rfl

omit [Fintype B] [DecidableEq B] in
theorem metadata_challengeIndependent (ids : FingerprintPrefix.Setup) :
    CanonicalRequest.ChallengeIndependent shape binary.nPublic
      (metadata (Advice := Advice) (C := C) binary prime shape params ids) :=
  (metadata_setupOnly binary prime shape params ids).challengeIndependent

end LfzkV2.Current.ConcreteMetadata
