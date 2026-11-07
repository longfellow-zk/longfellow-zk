import LfzkV2.Current.SHALazy
import LfzkV2.Current.ProofOutput

/-! Parsing, canonical transcript transport and right-only verifier replay
change no Merkle slots. These identities connect the original raw prover to
the complete lazy Merkle experiment used by extraction. -/
noncomputable section
namespace LfzkV2.Current.SHAPrefix
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree ZeroKnowledge
open scoped Classical

variable {Raw D QT AT Out Result : Type}
variable (HT : QT → AT)

theorem left_map {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) (f : Out → Result) :
    TranscriptV2.Memoize.left HT (ProofOutput.map f body) =
      (TranscriptV2.Memoize.left HT body).map f := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [ProofOutput.map,TranscriptV2.Memoize.left,Merkle.RandomOracle.Tree.map,ih]
  | queryRight query next ih => exact ih (HT query)

private theorem left_weaken {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    TranscriptV2.Memoize.left HT (weakenRight body) = TranscriptV2.Memoize.left HT body := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenRight,TranscriptV2.Memoize.left,ih]
  | queryRight query next ih => exact ih (HT query)

private theorem left_weaken_add {left right : ℕ}
    (body : TwoOracleTree Raw D QT AT Out left right) (extra : ℕ) :
    TranscriptV2.Memoize.left HT (weakenRightAdd extra body) = TranscriptV2.Memoize.left HT body := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [weakenRightAdd,left_weaken,ih]

private theorem left_lift (left : ℕ) {right : ℕ} (body : Tree QT AT Out right) :
    TranscriptV2.Memoize.left HT (liftRightAt (QL := Raw) (DL := D) left body) =
      Tree.done (body.run HT).1 := by
  induction body with
  | done value => rfl
  | query query next ih => exact ih (HT query)

theorem left_bind {left right continuation : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (rec : Out → Tree QT AT Result continuation) :
    TranscriptV2.Memoize.left HT (body.bindRight rec) =
      (TranscriptV2.Memoize.left HT body).map (fun out => ((rec out).run HT).1) := by
  induction body with
  | done value => simp only [bindRight,left_weaken_add,left_lift,TranscriptV2.Memoize.left,Merkle.RandomOracle.Tree.map]
  | queryLeft query next ih => simp only [bindRight,TranscriptV2.Memoize.left,ih,Merkle.RandomOracle.Tree.map]
  | queryRight query next ih => exact ih (HT query)

section Transport
variable {Input Point : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Input valid) (outside : Input → AT)
variable (typed : Point → AT)

theorem left_program {left right : ℕ} (body : TwoOracleTree Raw D Input AT Out left right) :
    TranscriptV2.Memoize.left typed (codec.program outside body) =
      TranscriptV2.Memoize.left (codec.oracle outside typed) body := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [ByteOracleTransport.Codec.program,TranscriptV2.Memoize.left,ih]
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none => simpa only [ByteOracleTransport.Codec.program,decoded,left_weaken,
          TranscriptV2.Memoize.left,ByteOracleTransport.Codec.oracle] using ih (outside query)
      | some point => simpa only [ByteOracleTransport.Codec.program,decoded,
          TranscriptV2.Memoize.left,ByteOracleTransport.Codec.oracle] using ih (typed point.val)

end Transport

variable [DecidableEq Raw]

theorem recorded_slots {size left right : ℕ} (tape : Fin size → D) (dflt : D)
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List Raw)
    (past : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    (lazyRun tape dflt (TranscriptV2.Memoize.left HT (Observer.record past body)) seen).2.1 =
      (lazyRun tape dflt (TranscriptV2.Memoize.left HT body) seen).2.1 := by
  induction body generalizing seen past with
  | done value => rfl
  | queryLeft query next ih =>
      simp only [Observer.record,TranscriptV2.Memoize.left,lazyRun_query]
      exact ih _ _ _
  | queryRight query next ih => exact ih (HT query) seen _

theorem recorded_value {size left right : ℕ} (tape : Fin size → D) (dflt : D)
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List Raw)
    (past : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    (((fixLeft tape dflt (Observer.record past body) seen).run HT).1).1 =
      ((fixLeft tape dflt body seen).run HT).1 := by
  induction body generalizing seen past with
  | done value => rfl
  | queryLeft query next ih => simp only [Observer.record,fixLeft]; exact ih _ _ _
  | queryRight query next ih => simp only [Observer.record,fixLeft,Tree.run_query]; exact ih (HT query) seen _

variable [Inhabited D]

/-- A prefix of the complete lazy slot layout replays against the complete
oracle, even when its result still contains the original serialized proof. -/
theorem run_of_prefix {size left right fuel : ℕ} {Value : Type}
    (tape : Fin size → D) (body : TwoOracleTree Raw D QT AT Out left right)
    (complete : Tree Raw D Value fuel)
    (contains : (lazyRun tape default (TranscriptV2.Memoize.left HT body) []).2.1 <+:
      Merkle.MH.runSlots size complete tape) :
    (Observer.run (Merkle.MH.runOracle size complete tape) HT body).1 =
      ((fixLeft tape default body []).run HT).1 := by
  have slots : (lazyRun tape default (Observer.fixTranscript HT body) []).2.1 <+:
      Merkle.MH.runSlots size complete tape := by
    simpa only [Observer.fixTranscript,recorded_slots] using contains
  have same := congrArg Prod.fst (lazyRun_run_eq_of_prefix tape default
    (Observer.fixTranscript HT body) [] (Merkle.MH.runOracle size complete tape) _ (fun _ => rfl) slots)
  rw [Observer.fixTranscript_run] at same
  have output := congrArg Prod.fst same
  change (Observer.run (Merkle.MH.runOracle size complete tape) HT body).1 =
    (lazyRun tape default (TranscriptV2.Memoize.left HT (Observer.record [] body)) []).1.1 at output
  rw [SHALazy.lazy_output HT tape default (Observer.record [] body) [],recorded_value] at output
  exact output

end LfzkV2.Current.SHAPrefix
