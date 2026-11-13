import LfzkV2.Current.OracleWindow
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalView
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalColumns

/-! Identify the canonical encoder with the indexed commitment-hiding
schedule. Completion receives only disclosed columns. Programming those
leaves changes neither a numbered transcript query nor the final seal. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (configuration : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration
local notation "Column" => StrandCanonicalBackend.Leaf binary prime binaryNodes primeNodes repr shape setup configuration
local notation "Physical" => PhysicalColumn binary prime
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Request" => CanonicalRequest.Request shape binary.nPublic

def indexedCodec : Merkle.Indexed.Codec (Fin 2443 × MerkleNonce) Column Digest Bytes :=
  let first := RuntimeVerifier.first binary prime P R Public
  let second := RuntimeVerifier.second binary prime P R Public
  MerkleWireCodec.codec first.participant second.participant repr
  configuration.binaryField configuration.primeField setup.jointContext (by decide : 2443 ≤ 2^64)

def indexedDecoders : Merkle.Indexed.RoleDecoders
    (indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration) :=
  let first := RuntimeVerifier.first binary prime P R Public
  let second := RuntimeVerifier.second binary prime P R Public
  MerkleWireCodec.decoders first.participant second.participant repr
  configuration.binaryField configuration.primeField setup.jointContext (by decide : 2443 ≤ 2^64)

local notation "Codec" => indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration
local notation "Dec" => indexedDecoders binary prime binaryNodes primeNodes repr shape setup configuration
local notation "ToLeaf" => leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration

def nonleafOracle (read : StrandGhostMerkle.Observer.Other Codec Dec → Digest) : Strand.Oracle :=
  StrandGhostMerkle.Domains.extendOther
    (RuntimeVerifier.first binary prime P R Public).participant
    (RuntimeVerifier.second binary prime P R Public).participant repr
    configuration.binaryField configuration.primeField setup.jointContext (by decide) read

theorem nonleafOracle_agree (SHA : Strand.Oracle) (input : Strand.Input) :
    nonleafOracle binary prime binaryNodes primeNodes repr shape setup configuration
      (fun raw => SHA raw.val) input.encode = SHA input.encode :=
  StrandGhostMerkle.Domains.extendOther_agree _ _ _ _ _ _ _ SHA input

variable {blocks : ℕ} {Observed Context : Type} {postQueries : ℕ}
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)
local notation "Prepare" => prepare binary prime binaryNodes primeNodes repr shape setup configuration
  binaryCount metadata roundSampler

/-- This projection is defined only on the selected set. No unopened column
is required by canonical completion or its public simulator. -/
def disclosed (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (SHA : Strand.Oracle)
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      RandomOracle.Tree Bytes Digest Observed postQueries) :
    (Prepare request frontend backend SHA after).opened → Column := by
  cases backend with
  | none => exact fun index => False.elim (Finset.notMem_empty index.val index.property)
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => exact fun index => False.elim (Finset.notMem_empty index.val index.property)
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          exact fun index => ToLeaf (openedColumns binary prime indices opened index)

local notation "Disclosed" => disclosed binary prime binaryNodes primeNodes repr shape setup configuration
  binaryCount metadata roundSampler

theorem finish_installOpened (request : Request) (frontend : Body) (responses : ResponsePair B)
    (indices : Fin 84 ↪ Fin 2443)
    (physical : (OrderedOpening.query indices).coordinates → Physical)
    (opening : Merkle.Indexed.Opening 2443 (OrderedOpening.query indices).coordinates
      (Fin 2443 × MerkleNonce) Digest)
    (SHA : Strand.Oracle) (I : Finset (Fin 2443)) (nonces : I → MerkleNonce)
    (columns : I → Column) (leaves : Fin 2443 → Digest) :
    finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend responses indices physical opening
        (StrandGhostMerkle.Tree.installOpened Codec Dec SHA I nonces columns leaves) =
      finish binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend responses indices physical opening SHA := by
  apply finish_oracle_congr
  intro input
  exact StrandGhostMerkle.Observer.installOpened_other Codec Dec SHA I nonces columns leaves
    (StrandGhostMerkle.Domains.inputOther
      (RuntimeVerifier.first binary prime P R Public).participant
      (RuntimeVerifier.second binary prime P R Public).participant repr configuration.binaryField configuration.primeField
      setup.jointContext (by decide) input)

/-- The generic opened-only completion is the existing canonical completed
view, including its conflict branch, final seal, and later raw trace. -/
theorem complete_prepared (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (SHA : Strand.Oracle) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce) :
    ((context,prior),StrandGhostMerkle.Schedule.complete Codec Dec
      (Prepare request frontend backend SHA after) prior (Disclosed request frontend backend SHA after)
      ((after none).map fun observed => (none,observed)) SHA leaves (fun index => nonces index.val)) =
    fullView binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
      request context prior after leaves nonces frontend backend SHA := by
  cases backend with
  | none =>
      simp only [StrandGhostMerkle.Schedule.complete,prepare,disclosed,fullView,complete,
        StrandGhostMerkle.Observer.observe,StrandGhostMerkle.Tree.installOpened_empty,RandomOracle.Tree.run_map]
      simp
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none =>
          simp only [StrandGhostMerkle.Schedule.complete,prepare,disclosed,fullView,complete,
            StrandGhostMerkle.Observer.observe,StrandGhostMerkle.Tree.installOpened_empty,RandomOracle.Tree.run_map]
          simp
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          have sameFinish := finish_installOpened binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount metadata roundSampler request frontend responses indices (openedColumns binary prime indices opened)
            (StrandGhostMerkle.Tree.opening Codec SHA leaves (OrderedOpening.query indices).coordinates
              (fun index => nonces index.val)) SHA (OrderedOpening.query indices).coordinates
            (fun index => nonces index.val) (fun index => ToLeaf (openedColumns binary prime indices opened index)) leaves
          dsimp only [indexedCodec,indexedDecoders] at sameFinish
          simp only [StrandGhostMerkle.Schedule.complete,prepare,disclosed,fullView,complete,
            StrandGhostMerkle.Observer.observe,Equiv.symm_apply_apply,RandomOracle.Tree.run_map,
            indexedCodec,indexedDecoders]
          split_ifs
          · simp only [sameFinish]
          · rfl

/-- Specialize the committed-column invariant to the prepared encoder's
selected-column interface. The empty-set branches cover parser and sampler
failure without imposing successful execution as a premise. -/
theorem disclosed_respondHonest (primeCount : shape.primePublic = prime.nPublic)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R Public)
    (request : Request) (frontend : Body) (SHA : Strand.Oracle)
    (cells : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (tape : Backend.JointMasks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      RandomOracle.Tree Bytes Digest Observed postQueries) :
    Disclosed request frontend
        (respondHonest binary prime binaryNodes primeNodes repr shape setup configuration binaryCount primeCount
          metadata roundSampler batchingSamples request frontend SHA cells tape) SHA after =
      fun index => ToLeaf (committedColumns binary prime binaryNodes primeNodes cells tape index.val) := by
  generalize returned : respondHonest binary prime binaryNodes primeNodes repr shape setup configuration
    binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells tape = result
  cases result with
  | none =>
      funext index
      exact False.elim (Finset.notMem_empty index.val index.property)
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none =>
          funext index
          exact False.elim (Finset.notMem_empty index.val index.property)
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          funext index
          exact congrArg ToLeaf (congrFun
            (respondHonest_columns binary prime binaryNodes primeNodes repr shape setup configuration
              binaryCount primeCount metadata roundSampler batchingSamples request frontend SHA cells tape
              responses indices opened returned) index)

/-- The prepared tree makes only the caller's post-proof observer queries.
The canonical body and seal have already been computed by its captured
oracle, whose dependence is handled by `prepare_oracle_congr_reads`. -/
theorem prepare_run_congr (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (captured first second : Strand.Oracle)
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      RandomOracle.Tree Bytes Digest Observed postQueries)
    (same : ∀ output, ∀ raw ∈ OracleWindow.queries (after output), first raw = second raw)
    (columns : (Prepare request frontend backend captured after).opened → Column)
    (opening : Merkle.Indexed.Opening 2443 (Prepare request frontend backend captured after).opened
      (Fin 2443 × MerkleNonce) Digest) :
    ((Prepare request frontend backend captured after).finish columns opening).run first =
      ((Prepare request frontend backend captured after).finish columns opening).run second := by
  have later (output) : (after output).run first = (after output).run second := by
    apply RandomOracle.Tree.run_congr_on_trace
    intro entry member
    exact (same output entry.1 (OracleWindow.trace_mem_queries (after output) second entry member)).trans
      (RandomOracle.Tree.trace_sound (after output) second entry member).symm
  cases backend with
  | none => simp only [prepare,RandomOracle.Tree.run_map,later]
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => simp only [prepare,RandomOracle.Tree.run_map,later]
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          simp only [prepare,RandomOracle.Tree.run_map,later]

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
