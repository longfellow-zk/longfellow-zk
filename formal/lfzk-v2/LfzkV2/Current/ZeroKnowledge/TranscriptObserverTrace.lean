import LfzkV2.Current.ZeroKnowledge.TranscriptObserver
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment

/-! Canonical transport need not change the observer's request type to
retain malformed byte calls. The complete original trace is reconstructed
from the translated trace and the fixed complementary oracle. The lookup
tables below contain only answers already present in that trace. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.TranscriptObserverTrace
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical
variable {QM AM Point Raw AT Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)

def event : Observer.Event (QM := QM) (AM := AM) (QT := Raw) (AT := AT) →
    Option (Observer.Event (QM := QM) (AM := AM) (QT := Point) (AT := AT))
  | .inl qa => some (.inl qa)
  | .inr qa => (codec.decode qa.1).map fun point => .inr (point.val,qa.2)

private theorem weakenRight_run (HM : QM → AM) (HT : Point → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM Point AT Out left right) :
    Observer.run HM HT (weakenRight tree) = Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenRight,Observer.run,ih]
  | queryRight query next ih => simp only [weakenRight,Observer.run,ih]

theorem program_run (outside : Raw → AT) (HM : QM → AM) (HT : Point → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM Raw AT Out left right) :
    Observer.run HM HT (codec.program outside tree) =
      ((Observer.run HM (codec.oracle outside HT) tree).1,
        (Observer.run HM (codec.oracle outside HT) tree).2.filterMap (event codec)) := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [ByteOracleTransport.Codec.program,Observer.run,ih,List.filterMap_cons,event]
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none => simp only [ByteOracleTransport.Codec.program,decoded,weakenRight_run,Observer.run,
          ByteOracleTransport.Codec.oracle,ih,List.filterMap_cons,event,Option.map_none]
      | some point => simp only [ByteOracleTransport.Codec.program,decoded,Observer.run,
          ByteOracleTransport.Codec.oracle,ih,List.filterMap_cons,event,Option.map_some]

def lookup {Q A : Type} (fallback : A) : List (Q × A) → Q → A
  | [],_ => fallback
  | qa::tail,query => if query = qa.1 then qa.2 else lookup fallback tail query

private theorem lookup_sound {Q A : Type} (fallback : A) (trace : List (Q × A)) (H : Q → A)
    (sound : ∀ qa ∈ trace, qa.2 = H qa.1) (qa : Q × A) (present : qa ∈ trace) :
    lookup fallback trace qa.1 = qa.2 := by
  induction trace with
  | nil => contradiction
  | cons head tail ih =>
      by_cases same : qa.1 = head.1
      · rw [lookup,if_pos same,sound head List.mem_cons_self,sound qa present,same]
      · rw [lookup,if_neg same]
        apply ih (fun pair member => sound pair (List.mem_cons_of_mem _ member))
        rcases List.mem_cons.mp present with equal | member
        · cases equal
          exact False.elim (same rfl)
        · exact member

private theorem run_sound (HM : QM → AM) (HT : Point → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM Point AT Out left right) :
    ∀ qa ∈ (Observer.run HM HT tree).2,
      match qa with | .inl pair => pair.2 = HM pair.1 | .inr pair => pair.2 = HT pair.1 := by
  induction tree with
  | done value => intro qa member; contradiction
  | queryLeft query next ih =>
      intro qa member
      rcases List.mem_cons.mp member with equal | member
      · cases equal; rfl
      · exact ih _ qa member
  | queryRight query next ih =>
      intro qa member
      rcases List.mem_cons.mp member with equal | member
      · cases equal; rfl
      · exact ih _ qa member

private theorem run_congr (HM HM' : QM → AM) (HT HT' : Raw → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM Raw AT Out left right)
    (agree : ∀ qa ∈ (Observer.run HM HT tree).2,
      match qa with | .inl pair => HM' pair.1 = pair.2 | .inr pair => HT' pair.1 = pair.2) :
    Observer.run HM' HT' tree = Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      have answer := agree (.inl (query,HM query)) List.mem_cons_self
      simp only at answer
      simp only [Observer.run,answer]
      rw [ih (HM query) (fun qa member => agree qa (List.mem_cons_of_mem _ member))]
  | queryRight query next ih =>
      have answer := agree (.inr (query,HT query)) List.mem_cons_self
      simp only at answer
      simp only [Observer.run,answer]
      rw [ih (HT query) (fun qa member => agree qa (List.mem_cons_of_mem _ member))]

def restore (outside : Raw → AT) (defaultM : AM) (defaultT : AT)
    {left right : ℕ} (tree : TwoOracleTree QM AM Raw AT Out left right)
    (trace : List (Observer.Event (QM := QM) (AM := AM) (QT := Point) (AT := AT))) :=
  Observer.run (lookup defaultM (Observer.merkleTrace trace))
    (codec.oracle outside (lookup defaultT (Observer.transcriptTrace trace))) tree

/-- Original raw outputs and full traces are deterministic postprocessing
of the ordinary translated observer trace. No observer state is inserted
into the request delivered to the prover. -/
theorem restore_run (outside : Raw → AT) (defaultM : AM) (defaultT : AT)
    (HM : QM → AM) (HT : Point → AT) {left right : ℕ}
    (tree : TwoOracleTree QM AM Raw AT Out left right) :
    restore codec outside defaultM defaultT tree (Observer.run HM HT (codec.program outside tree)).2 =
      Observer.run HM (codec.oracle outside HT) tree := by
  let typed := Observer.run HM HT (codec.program outside tree)
  have sound := run_sound HM HT (codec.program outside tree)
  have mapped := congrArg Prod.snd (program_run codec outside HM HT tree)
  have observed (qa) (member : qa ∈ (Observer.run HM (codec.oracle outside HT) tree).2)
      (translated) (encoded : event codec qa = some translated) : translated ∈ typed.2 := by
    rw [mapped]
    exact List.mem_filterMap.mpr ⟨qa,member,encoded⟩
  unfold restore
  apply run_congr HM _ (codec.oracle outside HT) _ tree
  intro qa member
  cases qa with
  | inl pair =>
      have present := observed (.inl pair) member (.inl pair) rfl
      refine lookup_sound defaultM (Observer.merkleTrace typed.2) HM ?_ pair ?_
      · intro value inside
        obtain ⟨entry,entryMem,encoded⟩ := List.mem_filterMap.mp inside
        cases entry with
        | inl value => cases Option.some.inj encoded; exact sound _ entryMem
        | inr => cases encoded
      · exact List.mem_filterMap.mpr ⟨.inl pair,present,rfl⟩
  | inr pair =>
      cases decoded : codec.decode pair.1 with
      | none =>
          have actual := run_sound HM (codec.oracle outside HT) tree (.inr pair) member
          simpa only [ByteOracleTransport.Codec.oracle,decoded] using actual.symm
      | some point =>
          have present := observed (.inr pair) member (.inr (point.val,pair.2)) (by simp only [event,decoded,Option.map_some])
          simp only [ByteOracleTransport.Codec.oracle,decoded]
          refine lookup_sound defaultT (Observer.transcriptTrace typed.2) HT ?_ (point.val,pair.2) ?_
          · intro value inside
            obtain ⟨entry,entryMem,encoded⟩ := List.mem_filterMap.mp inside
            cases entry with
            | inl => cases encoded
            | inr value => cases Option.some.inj encoded; exact sound _ entryMem
          · exact List.mem_filterMap.mpr ⟨.inr (point.val,pair.2),present,rfl⟩

end LfzkV2.Current.ZeroKnowledge.TranscriptObserverTrace
