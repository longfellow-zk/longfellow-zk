import LfzkV2.Current.ZeroKnowledge.FrontendHistory
import LfzkV2.Current.ZeroKnowledge.OracleResponse

/-! History and message invariants for the single transition from batching
to opening. Its input is an abstract state, independent of how the honest
prover or public simulator generated the frontend. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.History
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice Key Base C : Type}

private theorem fresh_opening (body : Body g fields Advice (OpeningBody.Authentication g)) :
    ProtocolWrites.fresh body g.openingIndex =
      { responses := some (body.binaryBackend.response,body.primeBackend.response) } := by
  have hp : g.openingIndex.val ≠ g.primeStart := by
    have := g.roles_length
    have := g.openingIndex_last
    dsimp only [Geometry.primeStart]
    omega
  have hb : g.openingIndex.val ≠ g.binaryStart := by
    have := g.roles_length
    have := g.openingIndex_last
    dsimp only [Geometry.binaryStart]
    omega
  simp only [ProtocolWrites.fresh,g.get_openingIndex,if_neg hp,if_neg hb,
    reduceCtorEq,if_false,if_true,ProtocolWrites.frontendMessages]

/-- H/Z is fixed after the batching answer and before the next query.
Taking the state first fixes the query types before the oracle is elaborated. -/
theorem opening_properties
    (state : CompleteTranscript.State g fields Advice Key Base C)
    (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) → (Fin i.val → C) → Base)
    (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := OpeningBody.Authentication g) (Key := Key) (Base := Base) → Digest × C)
    (context : Key) (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (rank : state.rank.val+1 = g.openingIndex.val)
    (good : Good base H context state)
    (written : ∀ i, state.writes i = ProtocolWrites.fresh body
      ⟨i.val,by have := i.isLt; have := state.rank.isLt; omega⟩)
    (pending : state.pending = ProtocolWrites.fresh body
      ⟨state.rank.val,by have := g.openingIndex.isLt; omega⟩) :
    let next := CompleteTranscript.bind (CompleteTranscript.step base H state).2
      (fun writes => { writes with responses := some responses })
    next.rank.val = g.openingIndex.val ∧ Good base H context next ∧
      (∀ i, next.writes i = ProtocolWrites.fresh (OracleResponse.fillBoth body responses)
        ⟨i.val,by have := i.isLt; have := next.rank.isLt; omega⟩) ∧
      ∀ inside : next.rank.val < g.roles.length,
        next.pending = ProtocolWrites.fresh (OracleResponse.fillBoth body responses) ⟨next.rank.val,inside⟩ := by
  let next := CompleteTranscript.bind (CompleteTranscript.step base H state).2
    (fun writes => { writes with responses := some responses })
  have oldInside : state.rank.val < g.roles.length := by have := g.openingIndex.isLt; omega
  have before : state.rank.val < g.openingIndex.val := by omega
  have nextRank : next.rank.val = g.openingIndex.val := by
    dsimp only [next,CompleteTranscript.bind]
    rw [CompleteTranscript.step_query base H state oldInside]
    exact rank
  refine ⟨nextRank,bind_good base H context _ _ (step_good base H context state good),?_,?_⟩
  · let Written (current : CompleteTranscript.State g fields Advice Key Base C) : Prop :=
      ∀ i, current.writes i = ProtocolWrites.fresh (OracleResponse.fillBoth body responses)
        ⟨i.val,by have := i.isLt; have := current.rank.isLt; omega⟩
    have advanced : Written (CompleteTranscript.bind
        (CompleteTranscript.advance base state oldInside (H (CompleteTranscript.query base state oldInside)))
        (fun writes => { writes with responses := some responses })) := by
      intro i
      change Fin.snoc (α := fun _ : Fin (state.rank.val+1) => ProtocolWrites.Fresh g fields Advice)
        state.writes state.pending i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last,pending]
        exact (OracleResponse.freshBoth_before body responses _ before).symm
      · rw [Fin.snoc_castSucc,written]
        exact (OracleResponse.freshBoth_before body responses _ (j.isLt.trans before)).symm
    have actual := congrArg (fun pair => CompleteTranscript.bind pair.2
      (fun writes => { writes with responses := some responses }))
      (CompleteTranscript.step_query base H state oldInside)
    exact (congrArg Written actual).mpr advanced
  · intro inside
    have index : (⟨next.rank.val,inside⟩ : Fin g.roles.length) = g.openingIndex := Fin.ext nextRank
    rw [index,fresh_opening]
    rw [CompleteTranscript.step_query base H state oldInside]
    rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.History
