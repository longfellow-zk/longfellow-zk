import LfzkV2.Current.IdealProofRate7
import LfzkV2.Current.MdocRuntime
import LfzkV2.Current.MdocDefaults
import LfzkV2.Current.MdocIdentifiers

/-! The current mdoc specialization of the generic arbitrary-proof theorem.
Advice, sampling, backend coordinates and frontend annotations are constructed
from the trusted field representations and sparse circuit descriptions. -/
noncomputable section
namespace LfzkV2.Current.MdocProofRate7
open Application ApplicationSetup Finset
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "nodes" => ConcreteSetup.binaryNodes cantor
local notation "P" => MdocRuntime.binaryBackend bp nodes
local notation "R" => MdocRuntime.primeBackend pp
local notation "Geom" => MdocRuntime.geometry bp pp binary.plan prime.plan
local notation "repr" => MdocRuntime.representations scalars
local notation "Answer" => MdocRuntime.Answer bp pp binary.plan prime.plan nodes

local instance answerFintype : Fintype Answer := inferInstance

variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
local notation "shape" => MdocRuntime.shape bp pp binary.plan prime.plan bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "setup" => MdocIdentifiers.setup binary prime cantor scalars ids bounds
local notation "cfg" => MdocRuntime.configuration bp pp binary.plan prime.plan nodes scalars
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup (MdocRuntime.field_card binary.basis)
  (MdocRuntime.polynomialX binary.basis)
local notation "parameters" => MdocIdentifiers.parameters binary prime cantor scalars ids bounds

def metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := Answer) shape binary.nPublic :=
  ConcreteMetadata.metadata (g := Geom) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) bp pp shape
    (MdocRuntime.samples bp pp binary.plan prime.plan nodes) (Equiv.refl B) (Equiv.refl MdocRuntime.Prime)
    parameters setup scalars.binary.encode (MdocRuntime.generator binary.basis) MdocAdvice.decode

abbrev RawOutput := CanonicalRuntime.Request bp shape × Bytes
variable {tA calls Q : ℕ}
variable (body : TwoOracleTree Bytes Digest Bytes
  (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan
    (ConcreteSetup.binaryNodes cantor))
  (RawOutput binary prime bounds) tA calls)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

def defaultAnswer : Digest × Answer :=
  (MdocDefaults.digest,MdocRuntime.fallback bp pp binary.plan prime.plan nodes)

def rawEvent (mt : Fin (4886+tA) → Digest) (oracle : Bytes → Digest × Answer) : Prop :=
  IdealProofRate7.rawEvent (g := Geom) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (shared := 768) (maskBits := 256) (adviceBits := 10)
    (calls := calls) (tA := tA) (TM := 4886+tA)
    bp pp P R ((Geom).affineRows .binary) ((Geom).affineRows .prime)
    (MdocRuntime.binaryCapacity bp binary.plan) (MdocRuntime.primeCapacity pp prime.plan)
    repr shape setup cfg rfl rfl
    (metadata binary prime cantor scalars ids bounds) fits body
    (MdocDefaults.proof Geom B) (defaultAnswer binary prime cantor) mt oracle

def window := QueryRuntimeProbability.window (g := Geom) (fields := MdocRuntime.fields B)
  (Advice := MdocAdvice.Value) (QL := Bytes) (DL := Digest) (A := Digest × Answer)
  (Out := RawOutput binary prime bounds) (left := tA) (right := calls)
  repr shape setup (bp).nPublic fits body

abbrev Experiment := (Fin (4886+tA) → Digest) ×
  ({raw // raw ∈ window binary prime cantor scalars ids bounds body fits} → Digest × Answer)

def event (sample : Experiment binary prime cantor scalars ids bounds body fits) : Prop :=
  rawEvent binary prime cantor scalars ids bounds body fits sample.1
    (ByteOracleTransport.Codec.extendWindow
      (window binary prime cantor scalars ids bounds body fits) sample.2
      (fun _ => defaultAnswer binary prime cantor))

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

include bodyFits in
/-- Every finite adaptive adversary with at most Q distinct transcript
queries has the current rate-1/7 bound, including Q=0. The event parses the
actual proof bytes before checking the constructed verifier and extractor. -/
theorem window_ratio_le (fallback : Bytes → Digest × Answer)
    (hsupport : ∀ (mt : Fin (4886+tA) → Digest) (oracle : Bytes → Digest × Answer),
      (TranscriptV2.seen (fixLeft mt default body []) oracle).card ≤ Q) :
    ((univ.filter fun sample : Experiment binary prime cantor scalars ids bounds body fits =>
      rawEvent binary prime cantor scalars ids bounds body fits sample.1
        (ByteOracleTransport.Codec.extendWindow
          (window binary prime cantor scalars ids bounds body fits) sample.2 fallback)).card : ℚ) /
      Fintype.card (Experiment binary prime cantor scalars ids bounds body fits) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+tA*(tA-1)/2+(4886+tA)*(2*tA+(Geom).roles.length+Q+2) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  exact IdealProofRate7.ratio_le (g := Geom) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (shared := 768) (maskBits := 256) (adviceBits := 10)
    (calls := calls) (tA := tA) (TM := 4886+tA)
    bp pp P R ((Geom).affineRows .binary) ((Geom).affineRows .prime)
    (MdocRuntime.binaryCapacity bp binary.plan) (MdocRuntime.primeCapacity pp prime.plan)
    repr shape setup cfg rfl rfl
    (metadata binary prime cantor scalars ids bounds) fits body
    (MdocDefaults.proof Geom B) (defaultAnswer binary prime cantor)
    (ConcreteSetup.addresses bp pp nodes ConcreteSetup.primeNodes)
    (ConcreteSetup.addresses_eq bp pp nodes ConcreteSetup.primeNodes)
    bodyFits (Nat.le_max_left _ _) (Nat.le_max_left _ _) (by decide)
    prime.plan rfl (Nat.le_max_right _ _) binary.plan rfl (Nat.le_max_right _ _)
    hsupport (le_refl _) fallback

include bodyFits in
/-- Every finite adaptive adversary with at most Q distinct transcript
queries has the current rate-1/7 bound, including Q=0. The event parses the
actual proof bytes before checking the constructed verifier and extractor. -/
theorem ratio_le
    (hsupport : ∀ (mt : Fin (4886+tA) → Digest) (oracle : Bytes → Digest × Answer),
      (TranscriptV2.seen (fixLeft mt default body []) oracle).card ≤ Q) :
    ((univ.filter (event binary prime cantor scalars ids bounds body fits)).card : ℚ) /
      Fintype.card (Experiment binary prime cantor scalars ids bounds body fits) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+tA*(tA-1)/2+(4886+tA)*(2*tA+(Geom).roles.length+Q+2) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  exact window_ratio_le binary prime cantor scalars ids bounds body fits bodyFits
    (fun _ => defaultAnswer binary prime cantor) hsupport

end LfzkV2.Current.MdocProofRate7
