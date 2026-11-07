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
namespace LfzkV2.Current.ZeroKnowledge.Observer
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {QM AM QT AT Out : Type}

abbrev Event := (QM × AM) ⊕ (QT × AT)

def merkleTrace (trace : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) : List (QM × AM) :=
  trace.filterMap fun event => match event with | .inl qa => some qa | .inr _ => none

def transcriptTrace (trace : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) : List (QT × AT) :=
  trace.filterMap fun event => match event with | .inl _ => none | .inr qa => some qa

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

/-- Exchange oracle roles without changing the observer's output. -/
def swapSides : {left right : ℕ} → TwoOracleTree QM AM QT AT Out left right →
    TwoOracleTree QT AT QM AM Out right left
  | _,_,.done out => .done out
  | _,_,.queryLeft query next => .queryRight query fun answer => swapSides (next answer)
  | _,_,.queryRight query next => .queryLeft query fun answer => swapSides (next answer)

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

def map (f : Out → Other) : {left right : ℕ} →
    TwoOracleTree QM AM QT AT Out left right → TwoOracleTree QM AM QT AT Other left right
  | _,_,.done value => .done (f value)
  | _,_,.queryLeft query next => .queryLeft query fun answer => map f (next answer)
  | _,_,.queryRight query next => .queryRight query fun answer => map f (next answer)

theorem map_run (f : Out → Other) (HM : QM → AM) (HT : QT → AT)
    {left right : ℕ} (tree : TwoOracleTree QM AM QT AT Out left right) :
    run HM HT (map f tree) = (f (run HM HT tree).1,(run HM HT tree).2) := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [map,run,ih]
  | queryRight query next ih => simp only [map,run,ih]

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

/-- Fix the Merkle oracle, leaving only transcript calls as query nodes. -/
def fixMerkle (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    Tree QT AT (Out × List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) right :=
  TranscriptV2.Memoize.left HM (swapSides (record [] tree))

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

private theorem right_record (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right)
    (past : List (Event (QM := QM) (AM := AM) (QT := QT) (AT := AT))) :
    (TranscriptV2.Memoize.left HM (swapSides (record past tree))).run HT =
      (((run HM HT tree).1,past++(run HM HT tree).2),transcriptTrace (run HM HT tree).2) := by
  induction tree generalizing past with
  | done out => simp only [record,swapSides,TranscriptV2.Memoize.left,Tree.run_done,run,List.append_nil,
      transcriptTrace,List.filterMap_nil]
  | queryLeft query next ih =>
      simp only [record,swapSides,TranscriptV2.Memoize.left,run,ih,transcriptTrace,
        List.filterMap_cons,List.append_assoc,List.cons_append,List.nil_append]
  | queryRight query next ih =>
      simp only [record,swapSides,TranscriptV2.Memoize.left,Tree.run_query,run,ih,transcriptTrace,
        List.filterMap_cons,List.append_assoc,List.cons_append,List.nil_append]

/-- The full mixed trace is retained; only the outer residual trace is
projected to the oracle still being queried. -/
theorem fixTranscript_run (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    (fixTranscript HT tree).run HM = (run HM HT tree,merkleTrace (run HM HT tree).2) := by
  simpa only [fixTranscript,List.nil_append] using left_record HT HM tree []

theorem fixMerkle_run (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    (fixMerkle HM tree).run HT = (run HM HT tree,transcriptTrace (run HM HT tree).2) := by
  simpa only [fixMerkle,List.nil_append] using right_record HT HM tree []

/-- Both conditionings describe exactly one execution, including the
adaptive request and complete mixed trace returned in its view. -/
theorem conditionings_agree (HT : QT → AT) (HM : QM → AM) {left right : ℕ}
    (tree : TwoOracleTree QM AM QT AT Out left right) :
    ((fixTranscript HT tree).run HM).1 = ((fixMerkle HM tree).run HT).1 := by
  rw [fixTranscript_run,fixMerkle_run]

section Raw
variable {Point Raw A : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)
variable (outside : Raw → A) (HM : QM → AM)

/-- Fix Merkle first and then use the existing whole-prefix codec. The
recorded output retains every original raw call, even one rejected by the
canonical decoder. Those calls are answered by the fixed outside oracle. -/
def typedTranscript {left right : ℕ} (tree : TwoOracleTree QM AM Raw A Out left right) :
    Tree Point A (Out × List (Event (QM := QM) (AM := AM) (QT := Raw) (AT := A))) right :=
  codec.tree outside (fixMerkle HM tree)

theorem typedTranscript_run (HT : Point → A) {left right : ℕ}
    (tree : TwoOracleTree QM AM Raw A Out left right) :
    (typedTranscript codec outside HM tree).run HT =
      (run HM (codec.oracle outside HT) tree,
        codec.trace (transcriptTrace (run HM (codec.oracle outside HT) tree).2)) := by
  rw [typedTranscript,ByteOracleTransport.Codec.run_tree,fixMerkle_run]

end Raw
end LfzkV2.Current.ZeroKnowledge.Observer
