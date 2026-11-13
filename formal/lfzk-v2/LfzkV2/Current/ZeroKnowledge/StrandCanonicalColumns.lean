import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBridge

/-! The response-adaptive honest backend opens the same physical columns
that were committed before any batching or opening challenge. The column
map depends only on logical cells and the original backend mask tape. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open RecursivePolygero.Local
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
local notation "Cells" => Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
  Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265
local notation "Masks" => Backend.JointMasks binaryNodes primeNodes binary.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

def committedColumns (cells : Cells) (tape : Masks) : Fin 2443 → PhysicalColumn binary prime :=
  fun index =>
    ((OpeningBody.leafEquiv B (ConcreteSetup.rows binary.cells)).symm
      (MerkleCompiler.columnsEquiv B (ConcreteSetup.rows binary.cells) 0 2443
        (PolygeroZk.oracle (Backend.profileGeometry binaryNodes) (Backend.messages cells.1) tape.1) index),
      (OpeningBody.leafEquiv PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads))).symm
        (MerkleCompiler.columnsEquiv PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0 2443
          (PolygeroZk.oracle (Backend.profileGeometry primeNodes) (Backend.messages cells.2) tape.2) index))

variable {BE NE : Type} [Fintype BE] [Fintype NE]
variable (statements :
  ConstraintSystem B (ConcreteSetup.rows binary.cells) 0 265 BE ×
  ConstraintSystem PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0 265 NE)
variable (coins :
  Polygero.Coin B BE (ConcreteSetup.rows binary.cells) 0 12 ×
  Polygero.Coin PrimeField NE (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0 12)

omit [Fintype B] [DecidableEq B] in
theorem openedColumns_jointReal (indices : Fin 84 ↪ Fin 2443) (cells : Cells) (tape : Masks) :
    let proved := Backend.jointReal (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
      (OrderedOpening.query indices) cells statements coins tape
    openedColumns binary prime indices (proved.1.1,proved.2.1) =
      fun index => committedColumns binary prime binaryNodes primeNodes cells tape index.val := by
  rfl

omit [Fintype B] [DecidableEq B] in
/-- The response-dependent selector changes which columns are disclosed.
Every disclosed value is still read from the original committed oracle. -/
theorem openedColumns_adaptiveHonest
    (select : ResponsePair B → Option (Fin 84 ↪ Fin 2443)) (cells : Cells) (tape : Masks)
    (indices : Fin 84 ↪ Fin 2443)
    (opened : Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (OrderedOpening.query indices))
    (selected : (Backend.Adaptive.honest (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
      statements coins OrderedOpening.query select cells tape).2 = some ⟨indices,opened⟩) :
    openedColumns binary prime indices opened =
      fun index => committedColumns binary prime binaryNodes primeNodes cells tape index.val := by
  unfold Backend.Adaptive.honest at selected
  cases found : select (Backend.Adaptive.honestResponse
      (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) statements coins cells tape) with
  | none => simp only [found,Option.map_none,reduceCtorEq] at selected
  | some actual =>
      simp only [found,Option.map_some,Option.some.injEq] at selected
      cases selected
      exact openedColumns_jointReal binary prime binaryNodes primeNodes statements coins indices cells tape

section Canonical
variable {g : Geometry} {fields : Fields} {Advice C : Type} {blocks : ℕ}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)

/-- Parsing the actual statement and batching challenges changes no committed
column. This is the concrete bridge to the indexed commitment-hiding game. -/
theorem respondHonest_columns (configuration : RuntimeVerifier.Public (g := g) binary prime P R
    (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
    (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
    (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
    (roundSampler : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
      Merkle.RandomOracle.Tree TranscriptV2.Strand.Word TranscriptV2.Strand.Digest (Option C) blocks)
    (batchingSamples : C → RuntimeVerifier.RawSamples binary prime P R
      (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : CanonicalRequest.Request shape binary.nPublic)
    (frontend : Body g fields Advice (OpeningBody.Authentication g))
    (SHA : TranscriptV2.Strand.Oracle) (cells : Cells) (tape : Masks)
    (responses : ResponsePair B) (indices : Fin 84 ↪ Fin 2443)
    (opened : Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (OrderedOpening.query indices))
    (selected : respondHonest binary prime binaryNodes primeNodes repr shape setup configuration binaryCount primeCount
      metadata roundSampler batchingSamples request frontend SHA cells tape = some (responses,some ⟨indices,opened⟩)) :
    openedColumns binary prime indices opened =
      fun index => committedColumns binary prime binaryNodes primeNodes cells tape index.val := by
  simp only [respondHonest,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at selected
  obtain ⟨data,parsed,returned⟩ := selected
  apply openedColumns_adaptiveHonest (BE := Fin configuration.countBinary) (NE := Fin configuration.countPrime)
    binary prime binaryNodes primeNodes _ _ _ cells tape indices opened
  exact congrArg Prod.snd returned

end Canonical

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
