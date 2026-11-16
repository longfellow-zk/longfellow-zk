import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBridge

/-! When the challenge reader returns a value at every ordinary boundary, the
honest backend selects its opening and returns a complete response. The
backend's only failure is a reader abort: the opening reader runs only after
every earlier boundary has sampled, and then returns the reader's value. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits blocks : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
variable (fmt : Format g fields Advice binary.nPublic)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Request" => fmt.Request
local notation "Point" => fmt.Point
local notation "Masks" => Backend.JointMasks binaryNodes primeNodes binary.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Cells" => Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
  Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265

variable (configuration : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice) (Base := fmt.Base) (Key := fmt.Key) (C := C)
  (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : fmt.binaryPublic = binary.nPublic) (primeCount : fmt.primePublic = prime.nPublic)
variable (metadata : fmt.RequestMetadata C)
variable (roundSampler : fmt.Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)

/-- The reader returns a value at every ordinary boundary of the oracle. -/
def Sampled (SHA : Strand.Oracle) : Prop :=
  ∀ point : Point, point.rank < g.roles.length →
    TranscriptV2.StrandVerifier.sampled (StrandRuntime.history fmt.wire fmt.body) roundSampler SHA point

omit [Fintype B] [DecidableEq B] in
theorem sampled_round (SHA : Strand.Oracle)
    (all : ∀ (index : Fin g.roles.length) history block,
      TranscriptV2.StrandVerifier.sampled (StrandRuntime.history fmt.wire fmt.body) roundSampler SHA
        ((.round index history block : Point))) :
    Sampled binary fmt roundSampler SHA := by
  intro point rank
  cases point with
  | round index history block => exact all index history block
  | finalSeal history body => exact absurd rank (by simp [Input.rank])

/-- With every boundary sampled, the opening reader returns an opening. -/
theorem select_isSome (request : Request) (frontend : Body) (SHA : Strand.Oracle)
    (response : ResponsePair B) (sampled : Sampled binary fmt roundSampler SHA) :
    (select binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler
      request frontend SHA response).isSome := by
  have rank := fun n (h : n ≤ g.roles.length) => Chain.point_rank
    (M := (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes fmt configuration
      binaryCount metadata request).encoding.chain configuration.initialLink)
    ⟨responseBody binary prime binaryNodes primeNodes fmt configuration frontend response, fun _ => 0⟩
    (logicalOracle binary fmt roundSampler configuration.fallback SHA) h
  unfold select
  dsimp only
  rw [if_pos]
  · rw [Option.isSome_map]
    apply sampled
    exact lt_of_eq_of_lt (rank _ (Nat.le_of_lt g.openingIndex.isLt)) g.openingIndex.isLt
  · intro i
    apply sampled
    have := g.openingIndex.isLt
    exact lt_of_eq_of_lt (rank i.val (by omega)) (by omega)

/-- With the statement parsed and every boundary sampled, the honest backend
returns a response together with its selected opening. -/
theorem respondHonest_selected (draw : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes fmt configuration))
    (request : Request) (frontend : Body) (SHA : Strand.Oracle) (cells : Cells) (tape : Masks)
    (parsed : (CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes fmt configuration
      binaryCount primeCount metadata request frontend
      (logicalOracle binary fmt roundSampler configuration.fallback SHA)).isSome)
    (sampled : Sampled binary fmt roundSampler SHA) :
    ∃ response indices opened,
      respondHonest binary prime binaryNodes primeNodes fmt configuration binaryCount primeCount
        metadata roundSampler draw request frontend SHA cells tape = some (response,some ⟨indices,opened⟩) := by
  obtain ⟨data, hdata⟩ := Option.isSome_iff_exists.mp parsed
  obtain ⟨indices, hindices⟩ := Option.isSome_iff_exists.mp
    (select_isSome binary prime binaryNodes primeNodes fmt configuration binaryCount metadata roundSampler
      request frontend SHA
      (Backend.Adaptive.honestResponse (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
        (typedStatement binary prime binaryNodes primeNodes fmt configuration data.2.statement)
        (typedCoin binary prime binaryNodes primeNodes fmt configuration
          (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes fmt configuration
            binaryCount metadata draw request frontend
            (logicalOracle binary fmt roundSampler configuration.fallback SHA))) cells tape) sampled)
  simp only [respondHonest, hdata, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Backend.Adaptive.honest]
  rw [hindices, Option.map_some]
  exact ⟨_, _, _, rfl⟩

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
