import LfzkV2.Current.ZeroKnowledge.CompleteResponse
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation
import LfzkV2.Current.ZeroKnowledge.OraclePrimaryFreshness

/-! Actual inverse wire encoding of the two backend payloads at the current
profile's interpolation nodes. These identities connect the literal runtime
H arrays to the additive primary-mask formula used by opening freshness. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleResponseSamples
open Application ApplicationSetup ConcreteSetup RecursivePolygero Polynomial
open Frontend
open scoped Classical
variable {B Base Key C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := Base) (Key := Key) (C := C) (Salt := Fin 2443 × Digest))
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R cfg
local notation "Second" => RuntimeVerifier.second binary.description prime P R cfg

theorem binary_h (response : JointResponse.Response (First).participant (Second).participant) (i : Fin 361) :
    (CompleteVerifier.wireResponses binary.description prime binaryNodes primeNodes cfg response).1.h i =
      cfg.binaryField.symm (response.1.primary.val.eval
        (binaryNodes ⟨349+i.val,by have := i.isLt; omega⟩)) := by
  rfl

theorem binary_z (response : JointResponse.Response (First).participant (Second).participant) (i : Fin 698) :
    (CompleteVerifier.wireResponses binary.description prime binaryNodes primeNodes cfg response).1.z i =
      cfg.binaryField.symm (response.1.arithmetic.val.eval
        (binaryNodes ⟨349+i.val,by have := i.isLt; omega⟩)) := by
  rfl

theorem prime_h (response : JointResponse.Response (First).participant (Second).participant) (i : Fin 361) :
    (CompleteVerifier.wireResponses binary.description prime binaryNodes primeNodes cfg response).2.h i =
      cfg.primeField.symm (response.2.primary.val.eval
        (primeNodes ⟨349+i.val,by have := i.isLt; omega⟩)) := by
  rfl

theorem real_binary_primary (Q : LigeroFamily.QuerySet 2443 84)
    (logical : Backend.Cells B (ConcreteSetup.rows binary.description.cells) 265 ×
      Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (core : PolygeroCoreMasking.Tape B 84 (ConcreteSetup.rows binary.description.cells) 0)
    (masks : PolygeroMasking.Tape (Backend.profileGeometry binaryNodes).code (PolygeroZk.sumFunctional B 265))
    (primeTape : Backend.ProfileTape primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (values : Fin 361 → B) :
    (fun i : Fin 361 => cfg.binaryField
      ((CompleteVerifier.wireResponses binary.description prime binaryNodes primeNodes cfg
        (CompleteResponse.realResponses binary.description prime binaryNodes primeNodes cfg logical statement coin
          ((core,masks,(Response.evaluationEquiv B (OraclePrimaryFreshness.nodes binaryNodes)
            (OraclePrimaryFreshness.nodes_injective binaryNodes)).symm values),primeTape))).1.h i)) =
      values + fun i =>
        (PolygeroPrimaryMasking.batch (Backend.profileGeometry binaryNodes).positive coin.1.2
          (PolygeroZk.ordinaryRows (Backend.profileGeometry binaryNodes) (Backend.messages logical.1) core masks)).val.eval
            (OraclePrimaryFreshness.nodes binaryNodes i) := by
  funext i
  rw [binary_h,Equiv.apply_symm_apply]
  exact (Backend.real_primary_sample (Backend.profileGeometry binaryNodes) Q logical.1 statement.1 coin.1
    core masks (OraclePrimaryFreshness.nodes binaryNodes) (OraclePrimaryFreshness.nodes_injective binaryNodes)
    values i).trans (add_comm _ _)

end LfzkV2.Current.ZeroKnowledge.OracleResponseSamples
