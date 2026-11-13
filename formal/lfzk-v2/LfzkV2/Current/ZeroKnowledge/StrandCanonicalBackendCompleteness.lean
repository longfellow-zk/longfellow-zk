import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
import LfzkV2.Current.ZeroKnowledge.BackendCompleteness

/-! Completeness of the current canonical numbered-strand proof constructor. -/
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

theorem honest_family_verifies
    (cells : (Backend.Cells B (ConcreteSetup.rows binary.cells) 265 × Backend.Cells PrimeField (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)) (tape : (Backend.JointMasks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads)))
    (statement : JointResponse.Statement ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant)
    (coin : JointResponse.Coin ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant)
    (satisfied : statement.1.Satisfies (Backend.logical cells.1) ∧
      statement.2.Satisfies (Backend.logical cells.2)) (Q : QuerySet 2443 84) :
    ((RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).Verify ((Joint.Pair.statementEquiv (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant).symm statement)
      ((Joint.Pair.oracleEquiv ((RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant ((RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration))).participant).symm
        (PolygeroZk.oracle (Backend.profileGeometry binaryNodes) (Backend.messages cells.1) tape.1,
          PolygeroZk.oracle (Backend.profileGeometry primeNodes) (Backend.messages cells.2) tape.2))
      ((Joint.Pair.coinEquiv (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant).symm coin)
      ((Joint.Pair.responseEquiv (RuntimeVerifier.first binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant (RuntimeVerifier.second binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup configuration)).participant).symm
        (Backend.Adaptive.honestResponse (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
          statement coin cells tape)) Q := by
  change (∀ i : Fin 2, _)
  rw [Fin.forall_fin_two]
  constructor
  · exact Backend.real_verifies (Backend.profileGeometry binaryNodes) (by change 84+265+12 ≤ 2443; decide)
      Q cells.1 statement.1 coin.1 tape.1 satisfied.1
  · exact Backend.real_verifies (Backend.profileGeometry primeNodes) (by change 84+265+12 ≤ 2443; decide)
      Q cells.2 statement.2 coin.2 tape.2 satisfied.2


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
