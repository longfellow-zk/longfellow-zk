import LfzkV2.Current.ZeroKnowledge.StrandCanonicalColumns

/-! A successfully generated current honest backend supplies the actual
response, successful physical read and valid two-field algebraic checks. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open Merkle Merkle.MH LigeroFamily Frontend TranscriptV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic PrimeField shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ PrimeField)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)

variable {blocks : ℕ}


variable (configuration : RuntimeVerifier.Public (g := g) binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (roundSampler : (QueryRuntime.Runtime.Point repr shape setup binary.nPublic) → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option C) blocks)



abbrev honestOracle (cells : (Backend.Cells B (ConcreteSetup.rows binary.cells) 265 × Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)) (tape : (CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads))) : ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).Oracle :=
  (Joint.Pair.oracleEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm
    (PolygeroZk.oracle (Backend.profileGeometry binaryNodes) (Backend.messages cells.1) tape.1,
      PolygeroZk.oracle (Backend.profileGeometry primeNodes) (Backend.messages cells.2) tape.2)

private theorem selected_of_map {Choice : Type} {Opened : Choice → Type}
    (selection : Option Choice) (opening : (choice : Choice) → Opened choice)
    (choice : Choice) (values : Opened choice)
    (selected : selection.map (fun chosen => ⟨chosen,opening chosen⟩) =
      some (⟨choice,values⟩ : Sigma Opened)) : selection = some choice := by
  cases selection with
  | none => cases selected
  | some found => exact congrArg some (congrArg Sigma.fst (Option.some.inj selected))

theorem respondHonest_spec
    (primeCount : shape.primePublic = prime.nPublic)
    (draw : C → RuntimeVerifier.RawSamples binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))
    (request : (CanonicalRequest.Request shape binary.nPublic)) (frontend : (Current.Body g fields Advice (OpeningBody.Authentication g))) (SHA : Strand.Oracle) (cells : (Backend.Cells B (ConcreteSetup.rows binary.cells) 265 × Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)) (tape : (CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads)))
    (response : (ResponsePair B)) (indices : Fin 84 ↪ Fin 2443)
    (opened : Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (OrderedOpening.query indices))
    (generated : respondHonest binary prime binaryNodes primeNodes repr shape setup configuration binaryCount primeCount
      metadata roundSampler draw request frontend SHA cells tape = some (response,some ⟨indices,opened⟩)) :
    ∃ data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)) (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)),
      CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup configuration
        binaryCount primeCount metadata request frontend
        (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA) = some data ∧
      response = Backend.Adaptive.honestResponse (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
        data.2.statement
        (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup configuration
          binaryCount metadata draw request frontend
          (logicalOracle binary repr shape setup roundSampler configuration.fallback SHA)) cells tape ∧
      select binary prime binaryNodes primeNodes repr shape setup configuration binaryCount metadata roundSampler
        request frontend SHA response = some indices := by
  simp only [respondHonest,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at generated
  obtain ⟨data,parsed,returned⟩ := generated
  have responseEq := (congrArg Prod.fst returned).symm
  dsimp only [Backend.Adaptive.honest] at responseEq
  have picked := congrArg Prod.snd returned
  dsimp only [Backend.Adaptive.honest] at picked
  have selected := selected_of_map
    (Opened := fun choice : Fin 84 ↪ Fin 2443 => Backend.Adaptive.Opened (B := B) (N := PrimeField)
      (bw := ConcreteSetup.rows binary.cells)
      (nw := ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) (OrderedOpening.query choice))
    _ _ indices opened picked
  rw [← responseEq] at selected
  exact ⟨data,parsed,responseEq,selected⟩

/-- The actual committed physical columns are the same family columns
used by the shared indexed compiler. -/
theorem honest_columns (cells : (Backend.Cells B (ConcreteSetup.rows binary.cells) 265 × Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)) (tape : (CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads))) :
    (fun index => (leafEquiv binary prime binaryNodes primeNodes repr shape setup configuration) (committedColumns binary prime binaryNodes primeNodes cells tape index)) =
      ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).columnsEquiv (honestOracle binary prime binaryNodes primeNodes repr shape setup configuration cells tape) := by
  funext index side
  fin_cases side
  · exact Equiv.apply_symm_apply (OpeningBody.leafEquiv B (ConcreteSetup.rows binary.cells)) _
  · exact Equiv.apply_symm_apply
      (OpeningBody.leafEquiv PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads))) _

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
