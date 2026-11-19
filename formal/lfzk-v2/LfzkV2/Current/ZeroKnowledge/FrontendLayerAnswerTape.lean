import LfzkV2.Current.ZeroKnowledge.FrontendAnswerTape

/-! A layer's challenges read back from its returned answer tape. The two
terminal boundaries are retained exactly once; input-only assertions later
reuse the combine answer after its alpha coordinate. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape

open SumcheckV2
open scoped Classical
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F : Type} [Field F]
variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
variable (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)

theorem layer_extends {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) :
    Extends fallback state
      (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload).state := by
  rw [Prefix.layer_state]
  exact execute_extends base H side field fallback state _

theorem layer_last {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (last : Last fallback state) :
    Last fallback
      (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload).state := by
  rw [Prefix.layer_state]
  exact execute_last base H side field fallback state _ last

theorem layer_properties {n : ℕ} (state : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (fits : state.rank.val+n+2 ≤ g.roles.length) :
    let result := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload
    result.state.rank.val = state.rank.val+n+2 ∧
      result.point = (fun i => decode (lookup fallback result.state (state.rank.val+i.val)) 0) ∧
      result.scale = nonzero (lookup fallback result.state (state.rank.val+n)) ∧
      result.alpha = decode (lookup fallback result.state (state.rank.val+n+1)) 0 := by
  let rounds := readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader state payload.rounds
  let crossState := CompleteTranscript.frontend side rounds.2 (CompleteTranscript.mapMessage field.symm (.cross payload.cross))
  let terminal := CompleteTranscript.step base H crossState
  let claimsState := CompleteTranscript.frontend side terminal.2
    (CompleteTranscript.mapMessage field.symm (.claims payload.claimA payload.claimB))
  let combine := CompleteTranscript.step base H claimsState
  have roundsRank : rounds.2.rank.val = state.rank.val+n := by
    rw [Prefix.rounds_state,Frontend.ScheduleLength.execute_counter]
    simp only [Prefix.rounds,List.length_ofFn]
    exact Nat.min_eq_right (by omega)
  have crossInside : crossState.rank.val < g.roles.length := by
    change rounds.2.rank.val < _
    omega
  have terminalRank : terminal.2.rank.val = rounds.2.rank.val+1 := by
    rw [SimulationWrites.step_rank]
    exact Nat.min_eq_right (by change rounds.2.rank.val+1 ≤ _; omega)
  have claimsInside : claimsState.rank.val < g.roles.length := by
    change terminal.2.rank.val < _
    omega
  have combineRank : combine.2.rank.val = terminal.2.rank.val+1 := by
    rw [SimulationWrites.step_rank]
    exact Nat.min_eq_right (by change terminal.2.rank.val+1 ≤ _; omega)
  have throughCross : Extends fallback rounds.2 terminal.2 :=
    (bind_extends fallback rounds.2 _).trans (step_extends base H fallback crossState)
  have throughClaims : Extends fallback terminal.2 combine.2 :=
    (bind_extends fallback terminal.2 _).trans (step_extends base H fallback claimsState)
  have throughBoth := throughCross.trans throughClaims
  have points := rounds_point base H side field decode nonzero fallback state payload.rounds (by omega)
  have terminalAnswer := step_answer base H fallback crossState crossInside
  have combineAnswer := step_answer base H fallback claimsState claimsInside
  change combine.2.rank.val = _ ∧ rounds.1 = _ ∧ nonzero terminal.1 = _ ∧ decode combine.1 0 = _
  refine ⟨?_,?_,?_,?_⟩
  · rw [combineRank,terminalRank,roundsRank]
  · rw [points]
    funext i
    apply congrArg (fun value => decode value 0)
    exact (throughBoth.2 (state.rank.val+i.val) (by rw [roundsRank]; have := i.isLt; omega)).symm
  · apply congrArg nonzero
    rw [terminalAnswer]
    change lookup fallback terminal.2 rounds.2.rank.val = lookup fallback combine.2 (state.rank.val+n)
    rw [← roundsRank]
    exact (throughClaims.2 rounds.2.rank.val (by rw [terminalRank]; omega)).symm
  · apply congrArg (fun value => decode value 0)
    rw [combineAnswer]
    change lookup fallback combine.2 terminal.2.rank.val = lookup fallback combine.2 (state.rank.val+n+1)
    rw [terminalRank,roundsRank]

theorem layer_properties_into {n : ℕ} (state future : CompleteTranscript.State g fields Advice Key Base C)
    (payload : LayerPayload F n) (fits : state.rank.val+n+2 ≤ g.roles.length)
    (extended : Extends fallback
      (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload).state future) :
    let result := readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload
    result.state.rank.val = state.rank.val+n+2 ∧
      result.point = (fun i => decode (lookup fallback future (state.rank.val+i.val)) 0) ∧
      result.scale = nonzero (lookup fallback future (state.rank.val+n)) ∧
      result.alpha = decode (lookup fallback future (state.rank.val+n+1)) 0 := by
  have properties := layer_properties side field base H decode nonzero fallback state payload fits
  refine ⟨properties.1,?_,?_,?_⟩
  · rw [properties.2.1]
    funext i
    apply congrArg (fun value => decode value 0)
    exact (extended.2 (state.rank.val+i.val) (by rw [properties.1]; have := i.isLt; omega)).symm
  · rw [properties.2.2.1]
    apply congrArg nonzero
    exact (extended.2 (state.rank.val+n) (by rw [properties.1]; omega)).symm
  · rw [properties.2.2.2]
    apply congrArg (fun value => decode value 0)
    exact (extended.2 (state.rank.val+n+1) (by rw [properties.1]; omega)).symm

end LfzkV2.Current.ZeroKnowledge.Frontend.AnswerTape
