import LfzkV2.Current.ZeroKnowledge.OracleHonestRuntime
import LfzkV2.Current.ZeroKnowledge.FrontendGlobalCoins

/-! Exact product decomposition of the honest private coins around the
binary primary mask. Uniform polynomial coins become 361 independent field
evaluations through the existing interpolation equivalence. Every other
private coin is retained, including the frontend, selectors and nonces. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestCoins
open ApplicationSetup ConcreteSetup Frontend
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768) (nodes : Fin 2792 ↪ B)

structure Frame where
  frontend : CompleteHonest.Tape binary prime
  selectors : CompleteHonest.Masks (B := B)
  core : PolygeroCoreMasking.Tape B 84 (ConcreteSetup.rows binary.description.cells) 0
  masks : PolygeroMasking.Tape (Backend.profileGeometry nodes).code (PolygeroZk.sumFunctional B 265)
  prime : Backend.ProfileTape ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
  nonces : Fin 2443 → Digest

def assemble (frame : Frame binary prime nodes) (sample : Fin 361 → B) : HonestRuntime.Tape binary prime nodes where
  frontend := frame.frontend
  selectors := frame.selectors
  backend := ((frame.core,frame.masks,(Response.evaluationEquiv B (OraclePrimaryFreshness.nodes nodes)
    (OraclePrimaryFreshness.nodes_injective nodes)).symm sample),frame.prime)
  nonces := frame.nonces

def frameOf (tape : HonestRuntime.Tape binary prime nodes) : Frame binary prime nodes where
  frontend := tape.frontend
  selectors := tape.selectors
  core := tape.backend.1.1
  masks := tape.backend.1.2.1
  prime := tape.backend.2
  nonces := tape.nonces

def split (tape : HonestRuntime.Tape binary prime nodes) : Frame binary prime nodes × (Fin 361 → B) :=
  (frameOf binary prime nodes tape,(Response.evaluationEquiv B (OraclePrimaryFreshness.nodes nodes)
    (OraclePrimaryFreshness.nodes_injective nodes)) tape.backend.1.2.2)

def equivalence : (Frame binary prime nodes × (Fin 361 → B)) ≃ HonestRuntime.Tape binary prime nodes where
  toFun coins := assemble binary prime nodes coins.1 coins.2
  invFun := split binary prime nodes
  left_inv coins := by
    rcases coins with ⟨frame,sample⟩
    apply Prod.ext
    · rfl
    · exact (Response.evaluationEquiv B (OraclePrimaryFreshness.nodes nodes)
        (OraclePrimaryFreshness.nodes_injective nodes)).apply_symm_apply sample
  right_inv tape := by
    cases tape with
    | mk frontend selectors backend nonces =>
      rcases backend with ⟨⟨core,masks,primary⟩,prime⟩
      simp only [split,assemble,frameOf,Equiv.symm_apply_apply]

omit [Fintype B] in
theorem assemble_tapeAt (tape : HonestRuntime.Tape binary prime nodes) (sample : Fin 361 → B) :
    assemble binary prime nodes (frameOf binary prime nodes tape) sample =
      OracleHonestRuntime.tapeAt binary prime nodes tape sample := rfl

noncomputable abbrev frameFintype : Fintype (Frame binary prime nodes) := by
  letI : Fintype (PolygeroCoreMasking.Tape B 84 (ConcreteSetup.rows binary.description.cells) 0) := Fintype.ofFinite _
  letI : Fintype (PolygeroMasking.Tape (Backend.profileGeometry nodes).code (PolygeroZk.sumFunctional B 265)) := Fintype.ofFinite _
  letI : Fintype (Backend.ProfileTape ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) := Fintype.ofFinite _
  apply Fintype.ofInjective (fun frame : Frame binary prime nodes =>
    (frame.frontend,frame.selectors,frame.core,frame.masks,frame.prime,frame.nonces))
  intro first second same
  cases first
  cases second
  cases same
  rfl

noncomputable abbrev tapeFintype : Fintype (HonestRuntime.Tape binary prime nodes) :=
  letI := frameFintype binary prime nodes
  Fintype.ofEquiv (Frame binary prime nodes × (Fin 361 → B)) (equivalence binary prime nodes)

end LfzkV2.Current.ZeroKnowledge.OracleHonestCoins
