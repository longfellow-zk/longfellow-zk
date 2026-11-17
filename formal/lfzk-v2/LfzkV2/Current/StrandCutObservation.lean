import LfzkV2.Current.StrandCut

/-! The extractor's first-context cut is observable from raw SHA queries.
Only fresh node inputs affect the decoder registry. A repeated node keeps
its original name even if a missing parent has since become available;
PRF reads never contribute an authentication input to this cut. -/
noncomputable section
namespace LfzkV2.Current.StrandCutObservation
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T Key Out : Type} [DecidableEq P]

/-- Scan the actual raw observation in order, recording each node at its
first occurrence. Stop before the first node that decodes to the requested
context. Its own answer is therefore excluded from the extraction cut. -/
def scan (schema : History.Codec T) (bytes : P → Framing.Bytes) (context : T → Key) (key : Key) :
    (P → Option Digest) → List Entry → List (Point P PrfKey Word × Digest) → List (P × Digest)
  | _,_,[] => []
  | known,past,(.inr _,_)::rest => scan schema bytes context key known past rest
  | known,past,(.inl raw,digest)::rest =>
      match known raw with
      | some _ => scan schema bytes context key known past rest
      | none =>
          if (StrandSearch.decode schema bytes past raw).map context = some key then []
          else (raw,digest) :: scan schema bytes context key (Function.update known raw (some digest))
            (record past (bytes raw) digest) rest

/-- Scanning can discard queries or stop early, but cannot introduce a
Merkle preimage or an answer absent from the original raw observation. -/
theorem scan_mem (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (context : T → Key) (key : Key) (known : P → Option Digest) (past : List Entry)
    (trace : List (Point P PrfKey Word × Digest)) (raw : P) (digest : Digest)
    (member : (raw,digest) ∈ scan schema bytes context key known past trace) :
    (.inl raw,digest) ∈ trace := by
  induction trace generalizing known past with
  | nil => cases member
  | cons first rest ih =>
      rcases first with ⟨input,answer⟩
      cases input with
      | inr _ => exact List.mem_cons_of_mem _ (ih known past member)
      | inl address =>
          cases found : known address with
          | some value =>
              simp only [scan,found] at member
              exact List.mem_cons_of_mem _ (ih known past member)
          | none =>
              simp only [scan,found] at member
              by_cases stop : (StrandSearch.decode schema bytes past address).map context = some key
              · rw [if_pos stop] at member
                cases member
              · rw [if_neg stop] at member
                rcases List.mem_cons.mp member with equal | later
                · exact List.mem_cons.mpr (Or.inl (by cases equal; rfl))
                · exact List.mem_cons_of_mem _ (ih _ _ later)

/-- The original extraction cut in physical byte addresses. -/
def byteCut (schema : History.Codec T) (bytes : P → Framing.Bytes) (context : T → Key)
    (key : Key) (trace : List (Point P PrfKey Word × Digest)) : List (Framing.Bytes × Digest) :=
  (scan schema bytes context key (fun _ => none) [] trace).map fun qa => (bytes qa.1,qa.2)

omit [DecidableEq P] in
private theorem trace_node {fuel : ℕ} (context : T → Key) (raw : P) (logical : Option T)
    (next : Sample Digest Word → Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key) :
    StrandCut.trace context (.query (.inl (raw,logical)) next) H key =
      if logical.map context = some key then [] else
        (raw,(H (.inl (raw,logical))).1) ::
          StrandCut.trace context (next (H (.inl (raw,logical)))) H key := by
  cases logical <;> simp only [StrandCut.trace,beforeLabel,StrandCut.label,Option.map]
  all_goals split <;> rfl

omit [DecidableEq P] in
private theorem trace_prf {fuel : ℕ} (context : T → Key) (digest : PrfKey)
    (next : Sample Digest Word → Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key) :
    StrandCut.trace context (.query (.inr digest) next) H key =
      StrandCut.trace context (next (H (.inr digest))) H key := by
  simp only [StrandCut.trace,beforeLabel,StrandCut.label,reduceCtorEq,if_false]
  rfl

omit [DecidableEq P] in
private theorem trace_congr {Other : Type} {fuel extra : ℕ} (context : T → Key)
    (tree : Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (tree' : Tree (StrandSearch.Name P T) (Sample Digest Word) Other extra)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key)
    (same : (tree.run H).2 = (tree'.run H).2) :
    StrandCut.trace context tree H key = StrandCut.trace context tree' H key := by
  simp only [StrandCut.trace,beforeLabel_eq_takeWhile,same]

/-- The named first-context cut is exactly a function of the actual raw
observation, not of hidden challenge-stream coordinates or future answers.
Cache agreement is the coupling's existing source invariant. -/
theorem scan_eq_trace (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (context : T → Key) (key : Key) {fuel : ℕ} (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Entry)
    (H : StrandSearch.Name P T → Sample Digest Word) (G : Point P PrfKey Word → Digest)
    (agreement : ((StrandSearch.searchState schema bytes program state past).run H).1.1.2.Matches G) :
    scan schema bytes context key state.nodes past (program.run G).2 =
      StrandCut.trace context (StrandSearch.searchState schema bytes program state past) H key := by
  induction program generalizing state past with
  | done output => rfl
  | query point next ih =>
      have initial := Cache.Matches.of_extension
        (StrandSearch.searchState_extends schema bytes (.query point next) state past H) agreement
      cases point with
      | inl raw =>
          cases found : state.nodes raw with
          | some digest =>
              have current := initial.1 raw digest found
              have same := FreshOracle.relabel_weaken (StrandSearch.name schema bytes)
                (StrandSearch.advance bytes) (eagerState (StrandSearch.key bytes) (next digest) state) past H
              have agrees : ((StrandSearch.searchState schema bytes (next digest) state past).run H).1.1.2.Matches G := by
                simpa only [StrandSearch.searchState,eagerState,found,same] using agreement
              rw [trace_congr context _ (StrandSearch.searchState schema bytes (next digest) state past) H key
                (by simpa only [StrandSearch.searchState,eagerState,found] using congrArg Prod.snd same)]
              simpa only [Tree.run_query,scan,found,← current] using ih digest state past agrees
          | none =>
              let chosen := H (.inl (raw,StrandSearch.decode schema bytes past raw))
              let after := match state.streams (StrandSearch.key bytes raw chosen.1) with
                | some _ => state.node raw chosen.1
                | none => (state.node raw chosen.1).stream (StrandSearch.key bytes raw chosen.1) chosen.2
              let updated := record past (bytes raw) chosen.1
              have execution : StrandSearch.searchState schema bytes (.query (.inl raw) next) state past =
                  .query (.inl (raw,StrandSearch.decode schema bytes past raw)) (fun answer =>
                    StrandSearch.searchState schema bytes (next answer.1)
                      (match state.streams (StrandSearch.key bytes raw answer.1) with
                       | some _ => state.node raw answer.1
                       | none => (state.node raw answer.1).stream (StrandSearch.key bytes raw answer.1) answer.2)
                      (record past (bytes raw) answer.1)) := by
                simp only [StrandSearch.searchState,eagerState,found,FreshOracle.relabel,
                  StrandSearch.name,StrandSearch.advance]
                congr 1
                funext answer
                cases state.streams (StrandSearch.key bytes raw answer.1) <;> rfl
              have agrees : ((StrandSearch.searchState schema bytes (next chosen.1) after updated).run H).1.1.2.Matches G := by
                simpa only [execution,Tree.run_query] using agreement
              have afterMatches := Cache.Matches.of_extension
                (StrandSearch.searchState_extends schema bytes (next chosen.1) after updated H) agrees
              have current : G (.inl raw) = chosen.1 := afterMatches.1 raw chosen.1 (by
                dsimp [after]
                split <;> simp only [Cache.node,Cache.stream,Function.update_self])
              rw [execution,trace_node]
              simp only [Tree.run_query,scan,found,current]
              split
              · rfl
              · congr 1
                have later := ih chosen.1 after updated agrees
                have nodes : after.nodes = Function.update state.nodes raw (some chosen.1) := by
                  dsimp [after]
                  split <;> rfl
                simpa only [nodes] using later
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some row =>
              have current := initial.2 digest row found counter
              have same := FreshOracle.relabel_weaken (StrandSearch.name schema bytes)
                (StrandSearch.advance bytes) (eagerState (StrandSearch.key bytes) (next (row counter)) state) past H
              have agrees : ((StrandSearch.searchState schema bytes (next (row counter)) state past).run H).1.1.2.Matches G := by
                simpa only [StrandSearch.searchState,eagerState,found,same] using agreement
              rw [trace_congr context _ (StrandSearch.searchState schema bytes (next (row counter)) state past) H key
                (by simpa only [StrandSearch.searchState,eagerState,found] using congrArg Prod.snd same)]
              simpa only [Tree.run_query,scan,← current] using ih (row counter) state past agrees
          | none =>
              let chosen := H (.inr digest)
              let after := state.stream digest chosen.2
              have execution : StrandSearch.searchState schema bytes (.query (.inr (digest,counter)) next) state past =
                  .query (.inr digest) (fun answer => StrandSearch.searchState schema bytes
                    (next (answer.2 counter)) (state.stream digest answer.2) past) := by
                simp only [StrandSearch.searchState,eagerState,found,FreshOracle.relabel,
                  StrandSearch.name,StrandSearch.advance]
              have agrees : ((StrandSearch.searchState schema bytes (next (chosen.2 counter)) after past).run H).1.1.2.Matches G := by
                simpa only [execution,Tree.run_query] using agreement
              have afterMatches := Cache.Matches.of_extension
                (StrandSearch.searchState_extends schema bytes (next (chosen.2 counter)) after past H) agrees
              have current : G (.inr (digest,counter)) = chosen.2 counter :=
                afterMatches.2 digest chosen.2 (by simp only [after,Cache.stream,Function.update_self]) counter
              rw [execution,trace_prf]
              simpa only [Tree.run_query,scan,current,after,Cache.stream] using
                ih (chosen.2 counter) after past agrees

/-- A recorded search already contains the complete raw observation. Its
first-context cut can therefore be reconstructed without choosing any raw
oracle completion or observing any reserved but unused stream coordinate. -/
theorem recorded_scan_eq_trace (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (context : T → Key) (key : Key) {fuel : ℕ} (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Entry)
    (H : StrandSearch.Name P T → Sample Digest Word) :
    scan schema bytes context key state.nodes past
        ((StrandSearch.searchState schema bytes (recordTrace program) state past).run H).1.1.1.2 =
      StrandCut.trace context (StrandSearch.searchState schema bytes (recordTrace program) state past) H key := by
  let final := ((StrandSearch.searchState schema bytes (recordTrace program) state past).run H).1.1.2
  let G := final.raw 0
  have agreement : final.Matches G := Cache.matches_raw final 0
  have source := (StrandSearch.searchState_source schema bytes (recordTrace program) state past H G agreement).1
  simp only [run_recordTrace] at source
  have exactCut := scan_eq_trace schema bytes context key (recordTrace program) state past H G agreement
  simpa only [run_recordTrace,source] using exactCut

/-- Raw completion retained at the end of the actual named replay. -/
def completion {Result : Type} {fuel extra : ℕ} (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)
    (H : StrandSearch.Name P T → Sample Digest Word) : Point P PrfKey Word → Digest :=
  let tree := StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []
  let resume := fun cut => StrandSearch.searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2
  (((tree.bind resume).run H).1).1.2.raw 0

theorem completion_matches {Result : Type} {fuel extra : ℕ} (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)
    (H : StrandSearch.Name P T → Sample Digest Word) :
    let tree := StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []
    let resume := fun cut => StrandSearch.searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2
    (((tree.bind resume).run H).1).1.2.Matches (completion schema bytes program replay H) := by
  exact Cache.matches_raw _ 0

/-- The completed cache reproduces both observed runs, including the original
query table. Unused cache coordinates need not be uniformly distributed:
only functions of these two actual observations are transported below. -/
theorem completion_observation {Result : Type} {fuel extra : ℕ}
    (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)
    (H : StrandSearch.Name P T → Sample Digest Word) :
    (program.run (completion schema bytes program replay H),
      (replay (program.run (completion schema bytes program replay H)).1).run
        (completion schema bytes program replay H)) =
      StrandSearch.replayObservation schema bytes program replay H := by
  simp only [completion,Tree.run_bind]
  let cut := ((StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []).run H).1
  let finish := ((StrandSearch.searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2).run H).1
  have source := StrandSearch.replay_source schema bytes program replay H (finish.1.2.raw 0)
    (Cache.matches_raw finish.1.2 0)
  exact Prod.ext source.1 source.2

/-- The canonical raw observation determines the same extraction cut as
the grouped search. This is the only conversion needed by an extractor;
there is no separately reconstructed grouped verifier or grouped view. -/
theorem completion_cut {Result : Type} {fuel extra : ℕ}
    (schema : History.Codec T) (bytes : P → Framing.Bytes) (context : T → Key)
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key) :
    scan schema bytes context key (Cache.empty : Cache P PrfKey Digest Word).nodes []
        (program.run (completion schema bytes program replay H)).2 =
      StrandCut.trace context
        (StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []) H key := by
  have original := congrArg Prod.fst (completion_observation schema bytes program replay H)
  dsimp only at original
  rw [original]
  exact recorded_scan_eq_trace schema bytes context key program Cache.empty [] H

/-- Any event determined by the original query table and actual verifier
replay has the same probability in the raw and grouped experiments. In
particular, a bound on missing original queries does not acquire the
verifier's replay queries when transferred to the grouped experiment. -/
theorem completion_law [Fintype P] [Fintype T] {Result : Type} {fuel extra : ℕ}
    (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)
    (event : (Out × List (Point P PrfKey Word × Digest)) ×
      (Result × List (Point P PrfKey Word × Digest)) → Prop) :
    Bcs.FiniteProbability.density (fun G => event
      (program.run G,(replay (program.run G).1).run G)) =
      Bcs.FiniteProbability.density (fun H =>
        let G := completion schema bytes program replay H
        event (program.run G,(replay (program.run G).1).run G)) := by
  simp only [completion_observation]
  exact StrandSearch.replay_law schema bytes program replay event

end LfzkV2.Current.StrandCutObservation
