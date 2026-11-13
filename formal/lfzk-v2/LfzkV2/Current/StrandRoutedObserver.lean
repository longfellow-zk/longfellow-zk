import LfzkV2.Current.SHAOracle

/-! Single-SHA domain routing for a raw strand observer.
Recording precedes partial evaluation: fixed Merkle answers or fixed strand
answers remain in the original raw observation, without additional queries. -/
noncomputable section
namespace LfzkV2.Current.StrandRoutedObserver
open TranscriptV2.Framing Merkle.RandomOracle
open scoped Classical

variable {Raw D Context : Type}

def embed : {fuel : ℕ} → Tree Raw D Context fuel → TwoOracleTree Raw D PUnit PUnit Context fuel 0
  | _,.done value => .done value
  | _,.query raw next => .queryLeft raw fun answer => embed (next answer)

theorem embed_output {fuel : ℕ} (program : Tree Raw D Context fuel) (H : Raw → D) :
    Observer.run H (fun _ => PUnit.unit) (embed program) =
      ((program.run H).1,((program.run H).2.map Sum.inl)) := by
  induction program with
  | done value => rfl
  | query raw next ih => simp only [embed,Observer.run,Tree.run_query,ih,List.map_cons]

def routed (domain : Raw → Prop) (outside : Raw → D) {fuel : ℕ}
    (program : Tree Raw D Context fuel) : Tree Raw D (Context × List (Raw × D)) fuel :=
  (Observer.fixTranscript (fun _ : PUnit => PUnit.unit)
    (SHAOracle.observer domain outside (embed program))).map fun result =>
      (result.1.1,Observer.merkleTrace result.1.2)

/-- Exact same output and full raw trace under the one merged oracle.
Only domain queries remain in the residual tree; the other answers use
precisely the same outside slice as public setup and commitment. -/
theorem routed_output (domain : Raw → Prop) (outside : Raw → D) {fuel : ℕ}
    (program : Tree Raw D Context fuel) (inside : Raw → D) :
    ((routed domain outside program).run inside).1 =
      program.run (SHAOracle.merge domain outside inside) := by
  rw [routed,Tree.run_map,Observer.fixTranscript_run]
  rw [SHAOracle.observer_output,embed_output]
  simp only [Observer.merkleTrace,List.filterMap_map]
  have identity : ∀ trace : List (Raw × D),
      trace.filterMap (fun qa => some qa) = trace := by
    intro trace
    simp
  exact congrArg (fun trace => ((program.run (SHAOracle.merge domain outside inside)).1,trace))
    (identity (program.run (SHAOracle.merge domain outside inside)).2)

theorem routed_trace (domain : Raw → Prop) (outside : Raw → D) {fuel : ℕ}
    (program : Tree Raw D Context fuel) (inside : Raw → D) :
    ((routed domain outside program).run inside).2 =
      ((program.run (SHAOracle.merge domain outside inside)).2.filter fun qa => decide (domain qa.1)) := by
  rw [routed,Tree.run_map,Observer.fixTranscript_run]
  change Observer.merkleTrace (Observer.run inside (fun _ : PUnit => PUnit.unit)
    (SHAOracle.route domain outside (Observer.record [] (embed program)))).2 = _
  rw [SHAOracle.route_trace,Observer.record_run,embed_output]
  generalize (program.run (SHAOracle.merge domain outside inside)).2 = trace
  induction trace with
  | nil => rfl
  | cons qa rest ih =>
      by_cases member : domain qa.1 <;> simp [Observer.merkleTrace,member] at ih ⊢ <;> exact ih

private theorem queries_map {P A Out Other : Type} [Fintype A] [DecidableEq P]
    {fuel : ℕ} (program : Tree P A Out fuel) (f : Out → Other) :
    OracleWindow.queries (program.map f) = OracleWindow.queries program := by
  induction program with
  | done value => rfl
  | query point next ih => simp only [Merkle.RandomOracle.Tree.map,OracleWindow.queries,ih]

/-- The residual all-branches window lies entirely in the varying domain.
Fixed answers therefore cannot accidentally be resampled by later finite
marginalization. -/
theorem routed_domain [Fintype D] [DecidableEq Raw] (domain : Raw → Prop)
    (outside : Raw → D) {fuel : ℕ} (program : Tree Raw D Context fuel) :
    ∀ raw ∈ OracleWindow.queries (routed domain outside program), domain raw := by
  intro raw member
  rw [routed,queries_map] at member
  have inside := ObserverWindow.queries_fixTranscript_subset (fun _ : PUnit => PUnit.unit)
    (SHAOracle.observer domain outside (embed program)) member
  exact SHAOracle.queries_route_domain domain outside (Observer.record [] (embed program)) raw inside

theorem routed_map_domain [Fintype D] [DecidableEq Raw] {Out : Type} (domain : Raw → Prop)
    (outside : Raw → D) {fuel : ℕ} (program : Tree Raw D Context fuel)
    (f : Context × List (Raw × D) → Out) :
    ∀ raw ∈ OracleWindow.queries ((routed domain outside program).map f), domain raw := by
  rw [queries_map]
  exact routed_domain domain outside program

end LfzkV2.Current.StrandRoutedObserver
