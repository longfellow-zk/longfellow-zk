import TranscriptV2.StrandCausality
import TranscriptV2.DigestCharging
import TranscriptV2.UnqueriedAnswer

/-! Charging the stored final seal for the two-query SHA construction. A
final node is in the STRAND domain and the stored seal is PRF counter zero.
The point-selection proof uses this separation, not a recoverable parent
preimage, a round counter, or an assumed adversarial query order. -/
namespace TranscriptV2.StrandSealCharging
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- A complete encoder determines the final node from its actual output.
The domains law separates finalization from challenge expansion. This local
interface does not assert acceptance of an entire application protocol. -/
structure Model (P D Out : Type) where
  node : Out → P
  prf : Out → D → P
  provided : Out → D
  domains : ∀ out digest, node out ≠ prf out digest

variable {P D Out : Type} [DecidableEq P]

/-- The submitted seal is correct, but its address was not queried by the
original program. Computing the address may replay arbitrarily many nodes;
those verifier reads are deliberately absent from `seen tree H`. -/
def UnqueriedSeal {fuel : ℕ} (point : Out → (P → D) → P) (provided : Out → D)
    (tree : Tree P D Out fuel) (H : P → D) : Prop :=
  let address := point (tree.run H).1 H
  address ∉ seen tree H ∧ H address = provided (tree.run H).1

/-- A selected seal address can depend on all other oracle coordinates.
If it does not depend on its own answer, one unqueried seal costs one digest
guess, irrespective of replay collisions or the number of earlier rounds. -/
theorem unqueriedSeal_ratio_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (point : Out → (P → D) → P) (provided : Out → D)
    (independent : ∀ out H H', AgreeOff (point out H) H H' → point out H = point out H')
    (tree : Tree P D Out fuel) :
    ((univ.filter (UnqueriedSeal point provided tree)).card : ℚ) /
      (Fintype.card D : ℚ)^Fintype.card P ≤ 1 / (Fintype.card D : ℚ) := by
  exact UnqueriedAnswer.ratio_le (fun out H => (point out H,provided out))
    (fun out H H' agree => Prod.ext (independent out H H' agree) rfl) tree

theorem unqueriedSeal_density_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (point : Out → (P → D) → P) (provided : Out → D)
    (independent : ∀ out H H', AgreeOff (point out H) H H' → point out H = point out H')
    (tree : Tree P D Out fuel) :
    Bcs.FiniteProbability.density (UnqueriedSeal point provided tree) ≤ 1 / (Fintype.card D : ℚ) := by
  simpa only [Bcs.FiniteProbability.density,Fintype.card_fun,Nat.cast_pow] using
    unqueriedSeal_ratio_le point provided independent tree

def Model.point (model : Model P D Out) (out : Out) (H : P → D) : P :=
  model.prf out (H (model.node out))

def bad {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel)
    (p : P) (H : P → D) (answer : D) : Prop :=
  model.point (tree.run H).1 H = p ∧ p ∉ seen tree H ∧ answer = model.provided (tree.run H).1

def Guess {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel)
    (H : P → D) : Prop := ∃ p, bad model tree p H (H p)

theorem required_query {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel)
    (H : P → D) (h : ¬Guess model tree H)
    (valid : H (model.point (tree.run H).1 H) = model.provided (tree.run H).1) :
    model.point (tree.run H).1 H ∈ seen tree H := by
  by_contra hm
  exact h ⟨model.point (tree.run H).1 H,rfl,hm,valid⟩

/-- The final state can be computed by verifier replay rather than supplied
by the prover. Stop replay before its seal read: if that read is absent from
the preceding verifier trace, a valid unguessed seal was queried by the
original search. The probability of `Guess` is still one digest guess, not
one guess per replay step. -/
theorem required_before_replay {Proof : Type} {fuel extra : ℕ}
    (model : Model P D Out) (search : Tree P D Proof fuel)
    (replay : Proof → Tree P D Out extra) (H : P → D)
    (unguessed : ¬Guess model (search.bind replay) H)
    (valid : H (model.point ((search.bind replay).run H).1 H) =
      model.provided ((search.bind replay).run H).1)
    (fresh : model.point ((search.bind replay).run H).1 H ∉
      seen (replay (search.run H).1) H) :
    model.point ((search.bind replay).run H).1 H ∈ seen search H := by
  have obtained := required_query model (search.bind replay) H unguessed valid
  rw [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append,Finset.mem_union] at obtained
  simp only [Tree.run_bind] at fresh ⊢
  exact obtained.resolve_right fresh

end TranscriptV2.StrandSealCharging
