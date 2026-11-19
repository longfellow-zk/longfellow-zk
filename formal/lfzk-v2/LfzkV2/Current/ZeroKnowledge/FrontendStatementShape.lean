import LfzkV2.Current.ApplicationViews
import LfzkV2.Current.StatementCompiler

/-! Affine statement dimensions follow from the existing compiler and
public circuit topology. Entries and quad fragments add no terminal rows;
the binary participant has two packing rows and each field has precisely
two selection rows. No caller supplies an equation-count certificate. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.StatementShape
open SumcheckV2 ApplicationSetup
open scoped Classical

theorem layers_stages {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) : circuit.layers = plan.frontend.stages.length := by
  induction plan with
  | input => rfl
  | inputEntry => rfl
  | layer _ _ ih =>
      simp only [Layered.Circuit.layers,FrontendSchedule.Plan.frontend,List.length_cons,ih]
      omega
  | entryLayer _ _ _ _ ih =>
      simp only [Layered.Circuit.layers,FrontendSchedule.Plan.frontend,List.length_cons,ih]
      omega

theorem packed_rows_length {B I J Slot Pad C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B]
    [Fintype I] [DecidableEq I] [Fintype J]
    (setup : FrontendVerifier.PackedSetup B I J Slot Pad)
    (payload : Layered.Replay.Payload setup.circuit) (decode : C → ℕ → B)
    (nonzero : C → Linear.TerminalSampling.Nonzero B) (answers : ℕ → C)
    (U delta : I → B) (A : B) :
    (setup.prepare payload decode nonzero answers U delta A).rows.length = setup.circuit.layers+2 := by
  have length := ApplicationViews.buildFrom_length zeroClaim
    (setup.circuit.proof (FrontendReplay.read decode nonzero setup.circuit setup.plan payload answers) 0)
    (FrontendVerifier.constraints setup.circuit setup.plan payload decode nonzero answers)
    (FrontendVerifier.constraints_built setup.circuit setup.plan payload decode nonzero answers)
  rw [ApplicationViews.circuit_proof_length] at length
  simpa only [Frontend.Packed.rows,FrontendVerifier.PackedSetup.prepare,Layered.Packed.virtualRows,Linear.Packed.rows,
    LfzkV2.Packed.Statement.rows,List.length_append,List.length_map,List.length_cons,List.length_nil]
      using congrArg (·+2) length

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => ZMod Current.Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B 768 256 10) (prime : PrimePublic P 768)
variable (primeData : PrimeData prime C) (card : Fintype.card B = Current.Adapter.Mdoc.binaryOrder)
variable (polynomialX : Bˣ) (bound : 2^10 ≤ Current.Adapter.Mdoc.quotientBound)
variable (data : BinaryData binary primeData (polynomialX^Current.Adapter.Mdoc.generatorExponent))

theorem decoded_frontends (system)
    (decoded : ApplicationSetup.decodeChecked binary prime primeData card polynomialX bound data = some system) :
    system.binary = data.frontend ∧ system.prime = primeData.frontend := by
  unfold ApplicationSetup.decodeChecked at decoded
  split at decoded
  · unfold ApplicationSetup.decode at decoded
    split at decoded
    · cases Option.some.inj decoded
      exact ⟨rfl,rfl⟩
    · contradiction
  · contradiction

theorem decoded_rows (system)
    (decoded : ApplicationSetup.decodeChecked binary prime primeData card polynomialX bound data = some system) :
    system.binary.rows = data.frontend.rows ∧
      system.primeRows = primeData.claim.rows data.eta data.mu ∧
      system.binaryLayout = CellLayout.selected binary.cells ∧
      system.primeLayout = CellLayout.Prime.layout prime.remaining prime.pads := by
  unfold ApplicationSetup.decodeChecked at decoded
  split at decoded
  · unfold ApplicationSetup.decode at decoded
    split at decoded
    · cases Option.some.inj decoded
      exact ⟨rfl,rfl,rfl,rfl⟩
    · contradiction
  · contradiction

/-- The prime statement has one unbatched layer row per circuit layer and
the native split row. -/
theorem prime_rows_length (eta mu : P) :
    (primeData.claim.rows eta mu).length = prime.circuit.layers+1 := by
  have length := ApplicationViews.buildFrom_length zeroClaim
    (prime.setup.circuit.proof (FrontendReplay.read primeData.decode primeData.nonzero prime.setup.circuit
      prime.setup.plan primeData.payload primeData.answers) 0)
    (FrontendVerifier.constraints prime.setup.circuit prime.setup.plan primeData.payload primeData.decode
      primeData.nonzero primeData.answers)
    (FrontendVerifier.constraints_built prime.setup.circuit prime.setup.plan primeData.payload primeData.decode
      primeData.nonzero primeData.answers)
  rw [ApplicationViews.circuit_proof_length] at length
  rw [Current.Prime.Claim.rows_length]
  simp only [PrimeData.claim,PrimeData.frontend,Composition.splitClaim,FrontendVerifier.PrimeSetup.prepare,
    Current.Prime.Claim.ofConstraints,Current.Prime.Claim.split,Current.Prime.nativeLayers,List.length_map]
  exact congrArg (·+1) length

theorem decoded_counts (plan : FrontendSchedule.Plan B binary.circuit)
    (primePlan : FrontendSchedule.Plan P prime.circuit)
    (g : Geometry) (geometry : g.binary = plan.frontend) (primeGeometry : g.prime = primePlan.frontend)
    (degree : g.packingDegree = binary.degree)
    (coinsB : WitnessSelection.Coins B binary.Original)
    (coinsP : WitnessSelection.Coins P prime.Original) (targetB : B × B) (targetP : P × P)
    (system)
    (decoded : ApplicationSetup.decodeChecked binary prime primeData card polynomialX bound data = some system) :
    (system.binary.rows ++ FingerprintRows.rows
      (fun i => system.binaryLayout (.inl i)) (fun i => system.binaryLayout (.inr i)) coinsB targetB).length =
        g.affineRows .binary ∧
    (system.primeRows ++ FingerprintRows.rows
      (fun i => system.primeLayout (.inl i)) (fun i => system.primeLayout (.inr i)) coinsP targetP).length =
        g.affineRows .prime := by
  have frontends := decoded_frontends binary prime primeData card polynomialX bound data system decoded
  have rows := decoded_rows binary prime primeData card polynomialX bound data system decoded
  have count := packed_rows_length data.setup data.payload data.decode data.nonzero data.answers data.U data.delta data.A
  have layers := layers_stages plan
  rw [← geometry] at layers
  have primeLayers := layers_stages primePlan
  rw [← primeGeometry] at primeLayers
  have nontrivial : g.packingDegree ≠ 1 := by rw [degree]; have := binary.degree_gt; omega
  constructor
  · rw [List.length_append,frontends.1]
    change (data.setup.prepare data.payload data.decode data.nonzero data.answers data.U data.delta data.A).rows.length+2 = _
    rw [count]
    change binary.circuit.layers+2+2 = _
    rw [layers]
    simp only [Geometry.affineRows,if_neg nontrivial]
  · rw [List.length_append,rows.2.1]
    change (primeData.claim.rows data.eta data.mu).length+2 = _
    rw [prime_rows_length,primeLayers]
    rfl

theorem compile_success (plan : FrontendSchedule.Plan B binary.circuit)
    (primePlan : FrontendSchedule.Plan P prime.circuit)
    (g : Geometry) (geometry : g.binary = plan.frontend) (primeGeometry : g.prime = primePlan.frontend)
    (degree : g.packingDegree = binary.degree)
    {k s n t : ℕ} (first : Application.FieldBackend B k s n t)
    (second : Application.FieldBackend P k s n t)
    (layout : StatementCompiler.Addresses first second binary.cells prime.remaining prime.pads)
    (coinsB : WitnessSelection.Coins B binary.Original)
    (coinsP : WitnessSelection.Coins P prime.Original) (targetB : B × B) (targetP : P × P)
    (system)
    (decoded : ApplicationSetup.decodeChecked binary prime primeData card polynomialX bound data = some system) :
    ∃ compiled, StatementCompiler.compile first second system layout (g.affineRows .binary) (g.affineRows .prime)
      coinsB coinsP targetB targetP = some compiled := by
  have counts := decoded_counts binary prime primeData card polynomialX bound data plan primePlan g geometry
    primeGeometry degree coinsB coinsP targetB targetP system decoded
  unfold StatementCompiler.compile StatementCompiler.equationIndex
  rw [dif_pos counts.1.symm,dif_pos counts.2.symm]
  exact ⟨_,rfl⟩

end LfzkV2.Current.ZeroKnowledge.Frontend.StatementShape
