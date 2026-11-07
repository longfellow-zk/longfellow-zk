import LfzkV2.Current.SHARouting

/-! Identify the left lazy tape with the single total oracle used by an
ordinary mixed execution. Trace recording is internal to the proof: it
does not give the adversary an oracle table or add a query. -/
noncomputable section
namespace LfzkV2.Current.SHALazy
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree ZeroKnowledge
open scoped Classical

variable {Raw D QT AT Out : Type} [DecidableEq Raw]
variable (HT : QT → AT)

omit [DecidableEq Raw] in
theorem left_run {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (HM : Raw → D) :
    (TranscriptV2.Memoize.left HT body).run HM =
      ((Observer.run HM HT body).1,Observer.merkleTrace (Observer.run HM HT body).2) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp [TranscriptV2.Memoize.left,Tree.run_query,Observer.run,Observer.merkleTrace,ih]
  | queryRight query next ih => simp [TranscriptV2.Memoize.left,Observer.run,Observer.merkleTrace,ih]

theorem lazy_output {size left right : ℕ} (tape : Fin size → D) (dflt : D)
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List Raw) :
    (lazyRun tape dflt (TranscriptV2.Memoize.left HT body) seen).1 =
      ((fixLeft tape dflt body seen).run HT).1 := by
  induction body generalizing seen with
  | done value => rfl
  | queryLeft query next ih =>
      simp only [TranscriptV2.Memoize.left,lazyRun_query,fixLeft]
      exact ih _ _
  | queryRight query next ih => exact ih (HT query) seen

theorem recorded_transcript {size left right : ℕ} (tape : Fin size → D) (dflt : D)
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List Raw)
    (past : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    Observer.transcriptTrace (((fixLeft tape dflt (Observer.record past body) seen).run HT).1.2) =
      Observer.transcriptTrace past ++ ((fixLeft tape dflt body seen).run HT).2 := by
  induction body generalizing seen past with
  | done value => simp only [Observer.record,fixLeft,Tree.run_done,List.append_nil]
  | queryLeft query next ih =>
      simp only [Observer.record,fixLeft]
      rw [ih]
      simp [Observer.transcriptTrace]
  | queryRight query next ih =>
      simp only [Observer.record,fixLeft,Tree.run_query]
      rw [ih]
      simp [Observer.transcriptTrace,List.append_assoc]

variable [Inhabited D]

/-- A bounded mixed program sees exactly the same proof and transcript
queries when its lazy left tape is presented as one total oracle function. -/
def oracle {size left right : ℕ} (tape : Fin size → D)
    (body : TwoOracleTree Raw D QT AT Out left right) : Raw → D :=
  Merkle.MH.runOracle size (Observer.fixTranscript HT body) tape

theorem recorded_run {size left right : ℕ} (tape : Fin size → D)
    (body : TwoOracleTree Raw D QT AT Out left right) :
    Observer.run (oracle HT tape body) HT body =
      ((fixLeft tape default (Observer.record [] body) []).run HT).1 := by
  have evaluated := congrArg Prod.fst
    (lazyRun_eq_run tape default (Observer.fixTranscript HT body) [] (oracle HT tape body) (fun _ => rfl))
  rw [Observer.fixTranscript_run] at evaluated
  exact evaluated.trans (lazy_output HT tape default (Observer.record [] body) [])

theorem transcript_run {size left right : ℕ} (tape : Fin size → D)
    (body : TwoOracleTree Raw D QT AT Out left right) :
    Observer.transcriptTrace (Observer.run (oracle HT tape body) HT body).2 =
      ((fixLeft tape default body []).run HT).2 := by
  rw [recorded_run HT tape body,recorded_transcript]
  rfl

section Setup
variable [DecidableEq QT]
variable {Key : Type} {left right rounds size checkFuel : ℕ}
variable (S : Bcs.TotalOracleCommit.Setup Raw D QT AT Out Key left right rounds)
variable (check : Out → Tree Raw D Unit checkFuel) (tape : Fin size → D)

variable [DecidableEq Key]

/-- Identify the exact lazy first-context trace with a prefix executed
against that same complete total oracle. The continuation's constant answer
is the retained cut implementation's empty-tape convention. -/
theorem setup_cut_run (key : Key) :
    Observer.merkleTrace (Observer.run (S.merkleOracle check tape HT) HT
      (Bcs.AdaptiveCommit.stopAt ((S.atOracle HT).cutIdx tape
          Bcs.TotalOracleCommit.Setup.emptyTape key)
        (S.body.bindRight fun out => Bcs.TotalOracleCommit.answerWith (fun _ => S.dflt) (S.recompute out)) [])).2 =
      (S.atOracle HT).cutTrace tape Bcs.TotalOracleCommit.Setup.emptyTape key := by
  let A := S.atOracle HT
  let index := A.cutIdx tape Bcs.TotalOracleCommit.Setup.emptyTape key
  have cutPrefix := (A.cutRun_seen_prefix tape Bcs.TotalOracleCommit.Setup.emptyTape index).trans
    (lazyRun_seen_prefix_bind tape default
      (fun oc : Out × (ℕ → AT) => (check oc.1).map fun _ => oc)
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape A.dflt A.joint []) [])
  have same := lazyRun_run_eq_of_prefix tape default
    (A.cutRun Bcs.TotalOracleCommit.Setup.emptyTape index) []
    (S.merkleOracle check tape HT) _ (fun _ => rfl) cutPrefix
  have cut : A.cutRun Bcs.TotalOracleCommit.Setup.emptyTape index =
      TranscriptV2.Memoize.left HT (Bcs.AdaptiveCommit.stopAt index
        (S.body.bindRight fun out => Bcs.TotalOracleCommit.answerWith (fun _ => S.dflt) (S.recompute out)) []) :=
    TranscriptV2.Memoize.actual_stop_bind HT S.dflt index S.body S.recompute [] []
  change _ = (lazyRun tape default (A.cutRun Bcs.TotalOracleCommit.Setup.emptyTape index) []).2.2
  rw [cut]
  rw [cut,left_run] at same
  exact congrArg Prod.snd same

end Setup

end LfzkV2.Current.SHALazy
