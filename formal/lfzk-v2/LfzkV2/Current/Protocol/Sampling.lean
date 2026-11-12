import LfzkV2.Current.Protocol.ExecutionSampler
import LfzkV2.Current.StrandRoleSampling

/-! Role-specific sampling data, independent of soundness composition. -/
noncomputable section
namespace LfzkV2.Current.Protocol.Sampling
open Application ApplicationSetup QueryRuntime Merkle.RandomOracle TranscriptV2
open scoped Classical

variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B c.k c.s c.n c.t) (R : FieldBackend N c.k c.s c.n c.t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "Answer" => IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "kind" => StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1)
local notation "RoleValue" => StrandRoleSampling.Value B N binary.Original prime.Original
  (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
local notation "RoleUnused" => StrandRoleSampling.Unused B N binary.Original prime.Original
  (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
  binaryCapacity primeCapacity

def values : Point → Type
  | .round index .. => RoleValue (kind (g.roles.get index))
  | .finalSeal .. => Answer

def unused : Point → Type
  | .round index .. => RoleUnused (kind (g.roles.get index))
  | .finalSeal .. => Unit

local instance answerFintype : Fintype Answer := by
  dsimp only [IdealRuntime.Answer,IdealSamples.Answer]
  infer_instance

local notation "Values" => values c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
local notation "Unused" => unused c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup

local instance valuesFintype (point : Point) : Fintype (Values point) := by
  cases point <;> dsimp only [values] <;> infer_instance

variable (binaryPlan : FrontendSchedule.Plan B binary.template)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryGeometry : binaryPlan.frontend = g.binary) (primeGeometry : primePlan.frontend = g.prime)
variable (binaryFits : binaryPlan.capacity ≤ binaryCapacity) (primeFits : primePlan.capacity ≤ primeCapacity)
variable (degreeFits : binary.degree ≤ binaryCapacity) (rowsFit : prime.circuit.layers+1 ≤ primeCapacity)
local notation "fitsRoles" => StrandRoleSampling.roleFits binaryCapacity primeCapacity g binaryPlan primePlan
  binaryGeometry primeGeometry binaryFits primeFits binary.degree (prime.circuit.layers+1) degreeFits rowsFit

/-- Only ordinary boundaries consume field samples. The final node's
identity factor is unused by the physical verifier; its seal is a raw PRF
answer, not an extra sampled field challenge. -/
def factor (point : Point) : Answer ≃ Values point × Unused point := by
  cases point with
  | round index history block =>
      exact StrandRoleSampling.factor B N binary.Original prime.Original
        (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
        binaryCapacity primeCapacity (kind (g.roles.get index)) (fitsRoles index)
  | finalSeal history body => exact (Equiv.prodUnique Answer Unit).symm

local notation "Factor" => factor c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit

variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic) (Key := FingerprintPrefix.Key binary.nPublic)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Fin c.n × MerkleNonce))
variable (sample : (point : QueryRuntime.Runtime.Point repr shape setup binary.nPublic) →
  Tree Strand.Word Digest (Option (values c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup point)) blocks)
def sampler (point : Point) : Tree Strand.Word Digest (Option Answer) blocks :=
  StrandSampling.read (Factor point) cfg.fallback (sample point)

end LfzkV2.Current.Protocol.Sampling

namespace LfzkV2.Current.Protocol
open Merkle.RandomOracle TranscriptV2
open scoped Classical
variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}

namespace Setup
variable (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))

abbrev RoleValue (point : S.Point) := Sampling.values c S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity S.repr S.shape S.fingerprint point

abbrev RoleUnused (point : S.Point) := Sampling.unused c S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity S.repr S.shape S.fingerprint point

abbrev roleFits := StrandRoleSampling.roleFits S.binaryCapacity S.primeCapacity g S.binaryPlan S.primePlan
  S.binaryGeometry S.primeGeometry S.binaryFits S.primeFits S.binary.degree (S.prime.circuit.layers+1)
  S.degreeFits S.rowsFit

abbrev factor (point : S.Point) := Sampling.factor c S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity S.repr S.shape S.fingerprint
  S.binaryPlan S.primePlan S.binaryGeometry S.primeGeometry S.binaryFits S.primeFits S.degreeFits S.rowsFit point

end Setup

/-- Role-specific sample values before filling unused answer coordinates. -/
structure SamplerData
    (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
    (blocks : ℕ) where
  sample : (point : S.Point) → Tree Strand.Word Digest (Option (S.RoleValue point)) blocks

/-- The accepted balanced-sampling assumption used by soundness. A zero
fiber remains permitted; no additional completeness or abort claim is made. -/
structure SamplerLaws
    {S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits)}
    {blocks : ℕ} (data : SamplerData S blocks) where
  fiber : S.Point → ℕ
  uniform : ∀ point value,
    (Finset.univ.filter fun stream => ((data.sample point).run stream).1 = some value).card = fiber point

structure Sampler
    (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
    (blocks : ℕ) where
  data : SamplerData S blocks
  laws : SamplerLaws data

namespace SamplerData
variable {S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits)}
variable {blocks : ℕ} (sampler : SamplerData S blocks)

abbrev execution : ExecutionSampler S blocks where
  sample := Sampling.sampler c S.binary S.prime S.P S.R S.countBinary S.countPrime
    S.binaryCapacity S.primeCapacity S.repr S.shape S.fingerprint S.binaryPlan S.primePlan
    S.binaryGeometry S.primeGeometry S.binaryFits S.primeFits S.degreeFits S.rowsFit S.cfg sampler.sample

end SamplerData
end LfzkV2.Current.Protocol
