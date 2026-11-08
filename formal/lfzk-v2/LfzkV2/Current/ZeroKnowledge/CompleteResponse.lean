import LfzkV2.Current.ZeroKnowledge.CompleteSimulationBody
import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteTranscript

/-! The honest H/Z write is a pure computation from the already recorded
frontend state and one joint batching answer. It receives no oracle and no
opening set. Thus it can be appended to the honest query tree before the
single opening answer is sampled or replaced. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteResponse
open Application ApplicationSetup RecursivePolygero LigeroFamily
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C)
  (Salt := Fin 2443 × MerkleNonce))
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second

def realResponses
    (logical : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) :
    JointResponse.Response (First).participant (Second).participant :=
  (PolygeroZk.payload (Backend.profileGeometry binaryNodes) (by change 0 < 84+265; decide) statement.1 coin.1
      (Backend.messages logical.1) tape.1,
    PolygeroZk.payload (Backend.profileGeometry primeNodes) (by change 0 < 84+265; decide) statement.2 coin.2
      (Backend.messages logical.2) tape.2)

theorem realResponses_eq (Q : QuerySet 2443 84)
    (logical : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) :
    realResponses binary prime binaryNodes primeNodes cfg logical statement coin tape =
      ((Backend.jointReal (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
        Q logical statement coin tape).1.2,
       (Backend.jointReal (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes)
        Q logical statement coin tape).2.2) := rfl

variable (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg)

def zero : Response g (fields .binary) × Response g (fields .prime) :=
  (⟨fun _ => cfg.binaryField.symm 0,fun _ => cfg.binaryField.symm 0⟩,
   ⟨fun _ => cfg.primeField.symm 0,fun _ => cfg.primeField.symm 0⟩)

def respond
    (logical : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (state : Frontend.CompleteTranscript.State g fields Advice Key Base C) (batchingAnswer : C) :
    Response g (fields .binary) × Response g (fields .prime) :=
  if inside : state.rank.val < g.roles.length then
    let point := Frontend.CompleteTranscript.query bindOnly state inside
    match RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic point state.past with
    | none => zero binary prime binaryNodes primeNodes cfg
    | some data => CompleteVerifier.wireResponses binary prime binaryNodes primeNodes cfg
        (realResponses binary prime binaryNodes primeNodes cfg logical data.2.statement
          (RuntimeVerifier.batchingDecoder binary prime P R cfg draw batchingAnswer) tape)
  else zero binary prime binaryNodes primeNodes cfg

theorem respond_parsed
    (logical : Backend.Cells B (ConcreteSetup.rows binary.cells) 265 ×
      Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (state : Frontend.CompleteTranscript.State g fields Advice Key Base C) (batchingAnswer : C)
    (inside : state.rank.val < g.roles.length) (data : Data)
    (parsed : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      (Frontend.CompleteTranscript.query bindOnly state inside) state.past = some data) :
    respond binary prime binaryNodes primeNodes cfg bindOnly hashPublic decodePublic draw
      logical tape state batchingAnswer =
      CompleteVerifier.wireResponses binary prime binaryNodes primeNodes cfg
        (realResponses binary prime binaryNodes primeNodes cfg logical data.2.statement
          (RuntimeVerifier.batchingDecoder binary prime P R cfg draw batchingAnswer) tape) := by
  simp only [respond,dif_pos inside,parsed]

end LfzkV2.Current.ZeroKnowledge.CompleteResponse
