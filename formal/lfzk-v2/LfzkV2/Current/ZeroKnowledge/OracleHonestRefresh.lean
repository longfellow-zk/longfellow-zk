import LfzkV2.Current.ZeroKnowledge.OracleHonestFreshness
import LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior
import LfzkV2.Current.ZeroKnowledge.RequestedExperiment

/-! The honest opening refresh with an adaptive public request. All
frontend messages and both real H/Z responses are computed by the actual
causal source program. Completion performs the ordinary authentication and
final seal against the returned oracle; aborts preserve the original table. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem fresh_map {Query Answer First Second : Type} {fuel : ℕ}
    (body : Tree Query Answer First fuel) (map : First → Second) (target : Second → Query)
    (H : Query → Answer) (fresh : MerklePrequery.fresh body (fun out => target (map out)) H) :
    MerklePrequery.fresh (body.map map) target H := by
  intro qa member same
  rw [Tree.run_map] at member
  unfold MerklePrequery.location at same
  rw [Tree.run_map] at same
  exact fresh qa member same
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)

local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Result" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (tape : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

local notation "b" => RequestedSimulator.requestedBinary binary prime primePlan shape
local notation "p" => RequestedSimulator.requestedPrime binary prime primePlan shape primeCount
local notation "configuration" => RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount
local notation "source" => RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount

abbrev Pending := (request : CanonicalRequest.Request shape binary.description.nPublic) ×
  HonestTranscript.Mdoc.Pending (b request) (p request) primePlan
    (Key := FingerprintPrefix.Key binary.description.nPublic)
    (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic) (C := C)

variable {Context View : Type} {preT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)
variable (before : Tree (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Context preT)

/-- The carried request records which public struct indexes the source
state. It is the same request selected by the earlier observer. -/
def next (sample : Fin 361 → B) (context : Context) :
    Tree Point (Digest × C) (Pending (C := C) binary prime primePlan repr shape setup primeCount) (1+HonestTranscript.Mdoc.fuel binary prime primePlan) :=
  let request := requestOf context
  (OracleHonestTree.tree (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
    binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample).map
    fun current => ⟨request,current⟩

theorem next_output (sample : Fin 361 → B) (context : Context) (H : Point → Digest × C) :
    ((next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf sample context).run H).1 =
      ⟨requestOf context,((OracleHonestTree.tree (b (requestOf context)) (p (requestOf context)) primePlan binaryNodes repr shape setup (configuration (requestOf context))
        binaryCount primeCount metadata (original (requestOf context)) (remaining (requestOf context)) (source (requestOf context) tape) (requestOf context) HM draw sample).run H).1⟩ := by
  unfold next
  rw [Tree.run_map]

def input (sample : Fin 361 → B) (current : Pending (C := C) binary prime primePlan repr shape setup primeCount) : Point :=
  let request := current.1
  OracleHonestTree.input (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
    binaryCount metadata (original request) (remaining request) (source request tape) request HM sample current.2

def active (sample : Fin 361 → B) (current : Pending (C := C) binary prime primePlan repr shape setup primeCount) : Prop :=
  let request := current.1
  OracleHonestTree.active (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
    binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample current.2

theorem internal_fresh (sample : Fin 361 → B) (context : Context) (H : Point → Digest × C) :
    MerklePrequery.fresh
      (next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf sample context)
      (input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM sample) H := by
  unfold next
  dsimp only
  apply fresh_map
  exact OracleHonestTree.internal_fresh (b (requestOf context)) (p (requestOf context)) primePlan binaryNodes repr shape setup (configuration (requestOf context))
    binaryCount primeCount metadata (original (requestOf context)) (remaining (requestOf context)) (source (requestOf context) tape)
    (requestOf context) HM draw H sample

/-- Honest authentication and the ordinary final seal use the returned
oracle. A rejected parser yields no proof and performs no programming. -/
def finish (sample : Fin 361 → B) (current : Pending (C := C) binary prime primePlan repr shape setup primeCount)
    (H : Point → Digest × C) : Option Result :=
  let request := current.1
  (OracleHonestTree.asPending (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
    binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample current.2).map
    (OracleHonestRuntime.finish (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
      binaryCount metadata (original request) (remaining request) (source request tape) request HM H sample)

variable (observe : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) → View)

def observation (sample : Fin 361 → B)
    (earlier : (Context × Pending (C := C) binary prime primePlan repr shape setup primeCount) × List (Point × (Digest × C)))
    (_answer : Option (Digest × C)) (H : Point → Digest × C) : View :=
  observe earlier.1.1
    (finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw
      sample earlier.1.2 H) H

end LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
