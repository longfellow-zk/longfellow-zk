import TranscriptV2.MemoizeCut
import LfzkV2.Current.ByteOracleTransport

/-! One observer may adaptively interleave the Merkle and transcript
oracles. Fixing either current oracle leaves a bounded tree over the other;
the output still contains the complete original mixed query/answer trace.
Neither translation supplies the observer with an unqueried oracle table.

The existing two-oracle syntax and total-oracle partial evaluator are reused.
Recording happens before canonical-byte transport, so malformed transcript
calls remain visible in the original observer trace as well. -/
noncomputable section
namespace LfzkV2.Current.Observer
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {QM AM QT AT Out : Type}

abbrev Event := (QM × AM) ⊕ (QT × AT)

def merkleTrace (trace : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) : List (QM × AM) :=
  trace.filterMap fun event => match event with | .inl qa => some qa | .inr _ => none

/-- Execute both current oracle functions in the original adaptive order.
Repeats read the same function coordinate, as they do in the runtime. -/
def run (HM : QM → AM) (HT : QT → AT) : {left right : ℕ} →
    TwoOracleTree QM AM QT AT Out left right →
      Out × List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))
  | _,_,.done out => (out,[])
  | _,_,.queryLeft query next =>
      let rest := run HM HT (next (HM query))
      (rest.1,.inl (query,HM query)::rest.2)
  | _,_,.queryRight query next =>
      let rest := run HM HT (next (HT query))
      (rest.1,.inr (query,HT query)::rest.2)

/-- Trace recording changes only the returned view, not either budget. -/
def record (past : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) :
    {left right : ℕ} → TwoOracleTree QM AM QT AT Out left right →
      TwoOracleTree QM AM QT AT
        (Out × List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) left right
  | _,_,.done out => .done (out,past)
  | _,_,.queryLeft query next => .queryLeft query fun answer =>
      record (past++[.inl (query,answer)]) (next answer)
  | _,_,.queryRight query next => .queryRight query fun answer =>
      record (past++[.inr (query,answer)]) (next answer)

variable {Other : Type}

/-- An observer may retain its entire earlier history as part of its
private output, at no additional query cost. -/
theorem record_run (past : List (Observer.Event (QM := QM) (AM := AM) (QT := QT) (AT := AT)))
    (HM : QM → AM) (HT : QT → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    run HM HT (record past tree) =
      (((run HM HT tree).1,past++(run HM HT tree).2),(run HM HT tree).2) := by
  induction tree generalizing past with
  | done value => simp only [record,run,List.append_nil]
  | queryLeft query next ih =>
      simp only [record,run,ih,List.append_assoc,List.singleton_append]
  | queryRight query next ih =>
      simp only [record,run,ih,List.append_assoc,List.singleton_append]

/-- Recording exposes exactly the original return value and mixed trace. -/
theorem record_output (past : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT)))
    (HM : QM → AM) (HT : QT → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    (run HM HT (record past tree)).1 = ((run HM HT tree).1,past++(run HM HT tree).2) :=
  congrArg Prod.fst (record_run past HM HT tree)

/-- Fix the transcript oracle, leaving only Merkle calls as query nodes. -/
def fixTranscript (HT : QT → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    Tree QM AM (Out × List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) left :=
  TranscriptV2.Memoize.left HT (record [] tree)

private theorem left_record (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right)
    (past : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) :
    (TranscriptV2.Memoize.left HT (record past tree)).run HM =
      (((run HM HT tree).1,past++(run HM HT tree).2),merkleTrace (run HM HT tree).2) := by
  induction tree generalizing past with
  | done out => simp only [record,TranscriptV2.Memoize.left,Tree.run_done,run,List.append_nil,
      merkleTrace,List.filterMap_nil]
  | queryLeft query next ih =>
      simp only [record,TranscriptV2.Memoize.left,Tree.run_query,run,ih,merkleTrace,
        List.filterMap_cons,List.append_assoc,List.cons_append,List.nil_append]
  | queryRight query next ih =>
      simp only [record,TranscriptV2.Memoize.left,run,ih,merkleTrace,
        List.filterMap_cons,List.append_assoc,List.cons_append,List.nil_append]

/-- The full mixed trace is retained; only the outer residual trace is
projected to the oracle still being queried. -/
theorem fixTranscript_run (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    (fixTranscript HT tree).run HM = (run HM HT tree,merkleTrace (run HM HT tree).2) := by
  simpa only [fixTranscript,List.nil_append] using left_record HT HM tree []

end LfzkV2.Current.Observer
