import LfzkV2.Current.ZeroKnowledge.StrandCanonicalSchedule
import LfzkV2.Current.ZeroKnowledge.StrandMerkleWindow
import LfzkV2.Current.ZeroKnowledge.StrandObserverWindow

/-! Oracle dependence of the existing canonical encoder and observer view.
These deterministic equalities are used to derive its raw execution support. -/
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

local notation "Codec" => indexedCodec binary prime binaryNodes primeNodes repr shape setup configuration
local notation "Dec" => indexedDecoders binary prime binaryNodes primeNodes repr shape setup configuration
local notation "ToLeaf" => leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration
local notation "RuntimePoint" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "History" => StrandRuntime.history (ProofBodyCodec.codec repr g)

variable {blocks : ℕ} {Observed Context : Type} {postQueries : ℕ}
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)

theorem reads_installOpened (first second : Strand.Oracle)
    (same : @StrandReadWindow.Agree RuntimePoint History first second)
    (I : Finset (Fin 2443)) (nonces : I → MerkleNonce) (columns : I → Column) (leaves : Fin 2443 → Digest) :
    @StrandReadWindow.Agree RuntimePoint History
      (StrandGhostMerkle.Tree.installOpened Codec Dec first I nonces columns leaves)
      (StrandGhostMerkle.Tree.installOpened Codec Dec second I nonces columns leaves) := by
  have off (H : Strand.Oracle) (input : Strand.Input) :
      StrandGhostMerkle.Tree.installOpened Codec Dec H I nonces columns leaves input.encode = H input.encode :=
    StrandGhostMerkle.Observer.installOpened_other Codec Dec H I nonces columns leaves
      (StrandGhostMerkle.Domains.inputOther
        (RuntimeVerifier.first binary prime P R Public).participant
        (RuntimeVerifier.second binary prime P R Public).participant repr configuration.binaryField configuration.primeField
        setup.jointContext (by decide) input)
  constructor
  · intro point
    exact (off first _).trans ((same.node point).trans (off second _).symm)
  · intro id parent counter
    exact (off first _).trans ((same.prf id parent counter).trans (off second _).symm)

theorem fullView_congr_reads (request : Request) (frontend : Body) (backend : Option (BackendOutput binary prime))
    (first second : Strand.Oracle) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := Advice) binary shape) →
      RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (reads : @StrandReadWindow.Agree RuntimePoint History first second)
    (nodes : ∀ index, index < 2443 → ∀ children, first ((Codec).nodeEnc index children) = second ((Codec).nodeEnc index children))
    (observer : ∀ output, ∀ raw ∈ OracleWindow.queries (after output), first raw = second raw) :
    fullView binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request context prior after leaves nonces frontend backend first =
      fullView binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request context prior after leaves nonces frontend backend second := by
  have later (output) : (after output).run first = (after output).run second := by
    apply RandomOracle.Tree.run_congr_on_trace
    intro entry member
    exact (observer output entry.1 (OracleWindow.trace_mem_queries (after output) second entry member)).trans
      (RandomOracle.Tree.trace_sound (after output) second entry member).symm
  cases backend with
  | none => simpa only [fullView,complete] using congrArg (fun result => ((context,prior),((none,result.1),result.2))) (later none)
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => simpa only [fullView,complete] using congrArg (fun result => ((context,prior),((none,result.1),result.2))) (later none)
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          let I := (OrderedOpening.query indices).coordinates
          let physical := openedColumns binary prime indices opened
          let columns := fun index : I => ToLeaf (physical index)
          let revealed := fun index : I => nonces index.val
          let installed (H : Strand.Oracle) := StrandGhostMerkle.Tree.installOpened Codec Dec H I revealed columns leaves
          let authentication (H : Strand.Oracle) := StrandGhostMerkle.Tree.opening Codec H leaves I revealed
          let output (H : Strand.Oracle) := finish binary prime binaryNodes primeNodes repr shape setup configuration
            binaryCount metadata roundSampler request frontend responses indices physical (authentication H) (installed H)
          have authenticationSame := StrandGhostMerkle.Tree.opening_congr Codec first second nodes leaves I revealed
          have outputSame : output first = output second := by
            exact (congrArg (fun auth => finish binary prime binaryNodes primeNodes repr shape setup configuration
              binaryCount metadata roundSampler request frontend responses indices physical auth (installed first))
              authenticationSame).trans
              (finish_oracle_congr_reads binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata
                roundSampler request frontend responses indices physical (authentication second) (installed first) (installed second)
                (reads_installOpened binary prime binaryNodes primeNodes repr shape setup configuration first second reads
                  I revealed columns leaves))
          have installedLater (out) : (after out).run (installed first) = (after out).run (installed second) := by
            apply RandomOracle.Tree.run_congr_on_trace
            intro entry member
            exact (StrandGhostMerkle.Swap.replace_congr _ first second _ entry.1
              (observer out entry.1 (OracleWindow.trace_mem_queries (after out) (installed second) entry member))).trans
              (RandomOracle.Tree.trace_sound (after out) (installed second) entry member).symm
          change
            (let result := if ∀ entry ∈ prior, ∀ index : I,
                  entry.1 ≠ (Codec).leafEnc ((index.val,revealed index),columns index) then
                (some (output first),installed first) else (none,first)
             ((context,prior),((result.1,((after result.1).run result.2).1),((after result.1).run result.2).2))) =
            (let result := if ∀ entry ∈ prior, ∀ index : I,
                  entry.1 ≠ (Codec).leafEnc ((index.val,revealed index),columns index) then
                (some (output second),installed second) else (none,second)
             ((context,prior),((result.1,((after result.1).run result.2).1),((after result.1).run result.2).2)))
          split_ifs
          · simp only [outputSame,installedLater]
          · simp only [later]

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
