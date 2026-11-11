import TranscriptV2.StrandTranscript
import TranscriptV2.StrandCausality
import TranscriptV2.DigestCharging
import Bcs.FiniteProbability
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

omit [DecidableEq P] in
theorem Model.point_off (model : Model P D Out) (out : Out) (H H' : P → D)
    (h : AgreeOff (model.point out H) H H') :
    model.point out H = model.point out H' := by
  unfold Model.point
  rw [h (model.node out) (model.domains out (H (model.node out)))]

def bad {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel)
    (p : P) (H : P → D) (answer : D) : Prop :=
  model.point (tree.run H).1 H = p ∧ p ∉ seen tree H ∧ answer = model.provided (tree.run H).1

def Guess {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel)
    (H : P → D) : Prop := ∃ p, bad model tree p H (H p)

/-- An unqueried stored final seal succeeds with probability at most 2⁻²⁵⁶
when D is a SHA-256 digest. The selected PRF input may depend on other SHA
answers and on an adaptively chosen complete body. -/
theorem guess_ratio_le [Fintype P] [Fintype D] [Nonempty D] [DecidableEq D]
    {fuel : ℕ} (model : Model P D Out) (tree : Tree P D Out fuel) :
    ((univ.filter (Guess model tree)).card : ℚ) /
      (Fintype.card D : ℚ)^Fintype.card P ≤ 1 / (Fintype.card D : ℚ) := by
  have same : Guess model tree = UnqueriedSeal model.point model.provided tree := by
    funext H
    apply propext
    constructor
    · rintro ⟨point,address,missing,answer⟩
      exact ⟨address ▸ missing,address ▸ answer⟩
    · rintro ⟨missing,answer⟩
      exact ⟨_,rfl,missing,answer⟩
  rw [same]
  exact unqueriedSeal_ratio_le model.point model.provided model.point_off tree

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

/-- The exact partition into non-PRF inputs and digest/counter inputs.
The output retains the final node chosen by replay and the received seal. -/
def splitModel {I : Type} (counter : I) : Model (Sum P (D × I)) D (P × D) where
  node out := .inl out.1
  prf _ digest := .inr (digest,counter)
  provided out := out.2
  domains _ _ := Sum.inl_ne_inr

open Framing Strand

abbrev Output := Absorbing × Bytes × Digest

/-- The domains law is proved from the actual Rust byte syntax. -/
def rawModel : Model Bytes Digest Output where
  node out := StrandTranscript.finalNodeInput out.1 out.2.1
  prf out digest := (Input.prf out.1.id digest 0).encode
  provided := fun out => out.2.2
  domains out digest := by
    unfold StrandTranscript.finalNodeInput
    cases hs : StrandTranscript.finalState out.1 out.2.1 with
    | root message => exact Ne.symm (Input.prf_ne_root out.1.id digest 0 message)
    | node id parent message => exact Ne.symm (Input.prf_ne_node out.1.id digest 0 id [parent] message)

@[simp] theorem raw_point (state : Absorbing) (body : Bytes) (provided : Digest) (H : Oracle) :
    rawModel.point (state,body,provided) H = StrandTranscript.finalSealInput state body H := rfl

def rawReplay (out : Output) : Tree Bytes Digest Digest 2 :=
  StrandTranscript.finalSeal out.1 out.2.1

/-- The final-node query is charged back to the original search rather than
paid for by the verifier's seal recomputation. Here the search output includes
its final transcript state; connecting that state to full protocol replay is
an additional end-to-end obligation. -/
theorem final_node_in_search {fuel : ℕ} (tree : Tree Bytes Digest Output fuel)
    (H : Oracle) (hseal : ¬Guess rawModel tree H)
    (hchain : ¬DigestCharging.Guess linearClaims (tree.bind rawReplay) H)
    (valid : H (rawModel.point (tree.run H).1 H) = rawModel.provided (tree.run H).1) :
    rawModel.node (tree.run H).1 ∈ seen tree H := by
  have hprf := required_query rawModel tree H hseal valid
  have hnode : rawModel.node (tree.run H).1 ∈ seen (tree.bind rawReplay) H := by
    simp only [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append,
      mem_union,rawReplay,StrandTranscript.finalSeal_run,List.map_cons,List.map_nil]
    exact Or.inr (by simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]; exact Or.inl rfl)
  apply DigestCharging.parent_in_search linearClaims tree rawReplay H hchain
    (rawModel.node (tree.run H).1) (rawModel.point (tree.run H).1 H) hnode hprf
  change H (rawModel.node (tree.run H).1) ∈
    linearClaims (Input.prf (tree.run H).1.1.id (H (rawModel.node (tree.run H).1)) 0).encode
  rw [linearClaims_prf]
  exact mem_singleton_self _

end TranscriptV2.StrandSealCharging
