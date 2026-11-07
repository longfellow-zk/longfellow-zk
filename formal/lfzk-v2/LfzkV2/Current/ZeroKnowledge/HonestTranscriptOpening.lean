import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdoc
import LfzkV2.Current.ZeroKnowledge.MerklePrequery

/-! The last honest prefix includes the one joint backend batching query.
The H/Z computation receives the already completed frontend and that answer;
it receives neither an oracle nor the later opening answer. The resulting
tree is therefore suitable for refreshing the entire opening answer before
using a fixed-opening backend change of masks. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
open Merkle.RandomOracle SumcheckV2 ApplicationSetup ConcreteSetup Frontend
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "State" => CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C)
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)
local notation "Frontend" => CompleteSimulation.RawResult binary prime primePlan Key Base C
local notation "Responses" => Response (CompleteSimulation.geometry binary prime primePlan) B ×
  Response (CompleteSimulation.geometry binary prime primePlan) P

structure Pending where
  frontend : CompleteSimulation.RawResult binary prime primePlan Key Base C
  batch : C
  state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C)

variable (coefficients : C →
  WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
variable (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
variable (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))

/-- `respond` is the local polynomial arithmetic, with private backend coins
captured in its closure. This interface supplies actual response values, not
a property asserting that an oracle-dependent program is causal. -/
def openingPrefix (respond : Frontend → C → Responses) :
    Tree Point (Digest × C) (Pending binary prime primePlan (Key := Key) (Base := Base) (C := C))
      (1+fuel binary prime primePlan) :=
  (program binary prime primePlan samples base coefficients context original remaining tape masks).bind fun frontend =>
    (step base frontend.state).map fun batched =>
      { frontend := frontend
        batch := batched.1
        state := CompleteTranscript.bind batched.2 fun writes =>
          { writes with responses := some (respond frontend batched.1) } }

theorem openingPrefix_output (respond : Frontend → C → Responses) (H : Point → Digest × C) :
    ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1 =
      let frontend := CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks
      let batched := CompleteTranscript.step base H frontend.state
      ({ frontend := frontend
         batch := batched.1
         state := CompleteTranscript.bind batched.2 fun writes =>
           { writes with responses := some (respond frontend batched.1) } } : Pending binary prime primePlan) := by
  unfold openingPrefix
  rw [Tree.run_bind,program_output,Tree.run_map,step_output]

theorem openingPrefix_progress (respond : Frontend → C → Responses) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank
      (CompleteTranscript.initial context samples.fallback)
      ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1.state
      ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).2 := by
  unfold openingPrefix
  refine RunProgress.bind _ _ (fun frontend : Frontend => frontend.state)
    (fun pending : Pending binary prime primePlan => pending.state) _ H
    (program_progress binary prime primePlan samples base coefficients context original remaining tape masks H) ?_
  intro frontend
  rw [Tree.run_map]
  exact (step_progress base frontend.state H).rebase rfl rfl

/-- Internal honest calls cannot have queried the next boundary. Only the
external observer's earlier trace can contain that exact input. The equality
here identifies the ordinary canonical target's counter, not a probabilistic
freshness or oracle-consistency assumption. -/
theorem openingPrefix_internal_fresh (respond : Frontend → C → Responses) (H : Point → Digest × C)
    (target : Point)
    (rank : Input.rank target =
      ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1.state.rank.val) :
    target ∉ (((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).2.map Prod.fst) := by
  intro member
  rcases List.mem_map.mp member with ⟨qa,member,same⟩
  have earlier := (openingPrefix_progress binary prime primePlan samples base coefficients context original remaining tape masks respond H).2 qa member
  rw [same,rank] at earlier
  exact (Nat.lt_irrefl _) earlier

/-- Replacing the later whole answer preserves the actual earlier frontend,
batching answer, H/Z values and full internal query trace. In particular the
earlier message prefix is not treated as fixed by assumption. -/
theorem openingPrefix_update (respond : Frontend → C → Responses) (H : Point → Digest × C)
    (target : Point) (answer : Digest × C)
    (rank : Input.rank target =
      ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1.state.rank.val) :
    (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run
      (Function.update H target answer) =
    (openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H := by
  apply Tree.run_congr_on_trace
  intro qa member
  have different : qa.1 ≠ target := by
    intro same
    exact openingPrefix_internal_fresh binary prime primePlan samples base coefficients context original remaining tape masks respond H target rank
      (List.mem_map.mpr ⟨qa,member,same⟩)
  rw [Function.update_of_ne different]
  exact (Tree.trace_sound _ H qa member).symm

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
