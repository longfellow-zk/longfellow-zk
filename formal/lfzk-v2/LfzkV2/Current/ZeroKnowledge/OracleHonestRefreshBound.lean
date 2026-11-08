import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshGames

/-! The complete abort-aware opening refresh for a request chosen by an
arbitrary earlier oracle program. The honest side uses the literal source
frontend, authentication and final seal. The programmed side draws one full
independent answer and returns the updated oracle for all later observation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem map_event_count {Mask Query Answer First Second : Type} [Fintype Mask] {fuel : ℕ}
    (body : Mask → Tree Query Answer First fuel) (map : First → Second)
    (event : Mask → Second → Prop) (H : Query → Answer) :
    (Finset.univ.filter fun mask => event mask (((body mask).map map).run H).1).card =
      (Finset.univ.filter fun mask => event mask (map ((body mask).run H).1)).card := by
  congr 1
  ext mask
  simp only [Finset.mem_filter,Tree.run_map]
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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
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

variable {Context View : Type} {preT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)
variable (before : Tree (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Context preT)
variable (observe : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) → View)

variable [Fintype C] [DecidableEq View]
local instance pointFintype : Fintype (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) := inferInstance
variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)

include fits bodyFits in
set_option backward.isDefEq.respectTransparency true in
theorem statClose (pivotOne : binary.basis 0 = 1)
    (hash : ∀ H sample, hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape HM (requestOf (before.run H).1) H sample) :
    StatClose ((preT : ℚ)/(2 : ℚ)^46208)
      (programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf before observe)
      (honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf before observe) := by
  let nextFn := next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf
  let inputFn := fun sample (_ : Context) => input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM sample
  let activeFn := fun sample (_ : Context) => active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw sample
  let observeFn := observation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw observe
  have localFresh : ∀ sample H, MerklePrequery.fresh (nextFn sample (before.run H).1) (inputFn sample (before.run H).1) H := by
    intro sample H
    exact internal_fresh binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf sample (before.run H).1 H
  have counts : ∀ H : Point → Digest × C,
      ((Finset.univ.filter fun sample =>
        activeFn sample (before.run H).1 ((nextFn sample (before.run H).1).run H).1 ∧
        inputFn sample (before.run H).1 ((nextFn sample (before.run H).1).run H).1 ∈ OracleRefreshPrior.keys before H).card : ℚ) /
        Fintype.card (Fin 361 → B) ≤ (preT : ℚ)/(2 : ℚ)^46208 := by
    intro H
    let request := requestOf (before.run H).1
    have counted := OracleHonestTree.active_point_queries (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
      binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw H
      fits bodyFits pivotOne (hash H) (OracleRefreshPrior.keys before H) preT (OracleRefreshPrior.keys_card before H)
    let body := fun sample => OracleHonestTree.tree (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
      binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample
    let inject := fun current => (⟨request,current⟩ : Pending (C := C) binary prime primePlan repr shape setup primeCount)
    let event := fun sample current =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw sample current ∧
      input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM sample current ∈
        OracleRefreshPrior.keys before H
    have same := map_event_count body inject event H
    have normalized := congrArg (fun n : ℕ => (n : ℚ)/Fintype.card (Fin 361 → B)) same
    have counted' : ((Finset.univ.filter fun sample => event sample (inject ((body sample).run H).1)).card : ℚ) /
        Fintype.card (Fin 361 → B) ≤ (preT : ℚ)/(2 : ℚ)^46208 := by
      dsimp only [event,inject,body,active,input]
      exact counted
    change ((Finset.univ.filter fun sample => event sample (((body sample).map inject).run H).1).card : ℚ) /
      Fintype.card (Fin 361 → B) ≤ (preT : ℚ)/(2 : ℚ)^46208
    have sameRatio :
        ((Finset.univ.filter fun sample => event sample (((body sample).map inject).run H).1).card : ℚ) /
          Fintype.card (Fin 361 → B) =
        ((Finset.univ.filter fun sample => event sample (inject ((body sample).run H).1)).card : ℚ) /
          Fintype.card (Fin 361 → B) := by
      convert normalized using 1 <;> congr
    exact sameRatio.le.trans counted'

  have bound := OracleRefreshPrior.statClose (Mask := Fin 361 → B) (Query := Point) (Answer := Digest × C)
    («Request» := Context) («Pending» := Pending (C := C) binary prime primePlan repr shape setup primeCount) (View := View)
    before nextFn inputFn activeFn observeFn (epsilon := (preT : ℚ)/(2 : ℚ)^46208) (by positivity) localFresh counts
  exact bound

end LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
