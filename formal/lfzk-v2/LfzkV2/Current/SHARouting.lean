import LfzkV2.Current.ZeroKnowledge.SHAOracle

/-! Splitting one SHA oracle preserves every transcript boundary, not just
the final output. The extractor keeps the Merkle-domain part of the original
prefix; auxiliary identifier queries are answered by the fixed complement.
The same statement holds at every distinct transcript-query cut. -/
noncomputable section
namespace LfzkV2.Current.SHARouting
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open ZeroKnowledge
open scoped Classical

variable {Raw D QT AT Out : Type}
variable (domain : Raw → Prop) (outside : Raw → D)

def keep : Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT) → Bool
  | .inl qa => decide (domain qa.1)
  | .inr _ => true

/-- The complete routed trace is exactly the original trace with auxiliary
SHA calls removed. Every transcript call, repeat and answer is retained. -/
theorem run {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (HM : Raw → D) (HT : QT → AT) :
    Observer.run HM HT (SHAOracle.route domain outside body) =
      ((Observer.run (SHAOracle.merge domain outside HM) HT body).1,
        (Observer.run (SHAOracle.merge domain outside HM) HT body).2.filter (keep domain)) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp [SHAOracle.route,member,Observer.run,SHAOracle.merge,ih,keep]
      · simp [SHAOracle.route,member,SHAOracle.weakenLeft_run,Observer.run,SHAOracle.merge,ih,keep]
  | queryRight query next ih =>
      simp only [SHAOracle.route,Observer.run,ih,List.filter_cons,keep,ite_true]

theorem transcript_filter (trace : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    Observer.transcriptTrace (trace.filter (keep domain)) = Observer.transcriptTrace trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | inl qa =>
          simp only [List.filter_cons,keep]
          split <;> simp_all [Observer.transcriptTrace]
      | inr qa => simpa [keep,Observer.transcriptTrace] using congrArg (List.cons qa) ih

theorem transcript_run {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (HM : Raw → D) (HT : QT → AT) :
    Observer.transcriptTrace (Observer.run HM HT (SHAOracle.route domain outside body)).2 =
      Observer.transcriptTrace (Observer.run (SHAOracle.merge domain outside HM) HT body).2 := by
  rw [run,transcript_filter]

section Queries
variable [Fintype D] [Fintype AT] [DecidableEq QT]

private theorem queries_weaken {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    ByteOracleTransport.Codec.allQueries (SHAOracle.weakenLeft body) =
      ByteOracleTransport.Codec.allQueries body := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [SHAOracle.weakenLeft,ByteOracleTransport.Codec.allQueries,ih]
  | queryRight query next ih => simp only [SHAOracle.weakenLeft,ByteOracleTransport.Codec.allQueries,ih]

theorem queries_subset {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    ByteOracleTransport.Codec.allQueries (SHAOracle.route domain outside body) ⊆
      ByteOracleTransport.Codec.allQueries body := by
  induction body with
  | done value => exact Finset.empty_subset _
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [SHAOracle.route,if_pos member,ByteOracleTransport.Codec.allQueries]
        exact Finset.biUnion_mono fun answer _ => ih answer
      · simp only [SHAOracle.route,if_neg member,queries_weaken,ByteOracleTransport.Codec.allQueries]
        intro raw inside
        exact Finset.mem_biUnion.mpr ⟨outside query,Finset.mem_univ _,ih (outside query) inside⟩
  | queryRight query next ih =>
      simp only [SHAOracle.route,ByteOracleTransport.Codec.allQueries]
      exact Finset.insert_subset_insert query (Finset.biUnion_mono fun answer _ => ih answer)

/-- Routing can remove program queries, while the canonical verifier image
in the finite oracle window stays unchanged. Keep the codec abstract here so
applications need not unfold its complete finite image to prove inclusion. -/
theorem window_subset {Point : Type} {valid : Point → Prop}
    [Fintype {point // valid point}]
    (codec : ByteOracleTransport.Codec Point QT valid)
    {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    codec.window (SHAOracle.route domain outside body) ⊆ codec.window body :=
  Finset.union_subset_union (queries_subset domain outside body) (Finset.Subset.refl _)

end Queries

variable [DecidableEq QT]

private theorem stop_weaken (index : ℕ) {left right : ℕ}
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List QT) :
    Bcs.AdaptiveCommit.stopAt index (SHAOracle.weakenLeft body) seen =
      SHAOracle.weakenLeft (Bcs.AdaptiveCommit.stopAt index body seen) := by
  induction body generalizing seen with
  | done value => rfl
  | queryLeft query next ih =>
      simp only [SHAOracle.weakenLeft,Bcs.AdaptiveCommit.stopAt]
      congr
      funext answer
      exact ih answer seen
  | queryRight query next ih =>
      simp only [SHAOracle.weakenLeft,Bcs.AdaptiveCommit.stopAt]
      split <;> simp only [SHAOracle.weakenLeft]
      exact congrArg (TwoOracleTree.queryRight query) (funext fun answer => ih answer _)

/-- Routing commutes with stopping before any distinct transcript answer.
Thus even a cut chosen by the proof's eventual commitment key is unchanged. -/
theorem stop (index : ℕ) {left right : ℕ}
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List QT) :
    SHAOracle.route domain outside (Bcs.AdaptiveCommit.stopAt index body seen) =
      Bcs.AdaptiveCommit.stopAt index (SHAOracle.route domain outside body) seen := by
  induction body generalizing seen with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [Bcs.AdaptiveCommit.stopAt,SHAOracle.route,if_pos member]
        exact congrArg (TwoOracleTree.queryLeft query) (funext fun answer => ih answer seen)
      · simp only [Bcs.AdaptiveCommit.stopAt,SHAOracle.route,if_neg member,stop_weaken]
        exact congrArg SHAOracle.weakenLeft (ih (outside query) seen)
  | queryRight query next ih =>
      simp only [Bcs.AdaptiveCommit.stopAt,SHAOracle.route]
      split <;> simp only [SHAOracle.route]
      exact congrArg (TwoOracleTree.queryRight query) (funext fun answer => ih answer _)

theorem cut_run (index : ℕ) {left right : ℕ}
    (body : TwoOracleTree Raw D QT AT Out left right) (seen : List QT)
    (HM : Raw → D) (HT : QT → AT) :
    Observer.run HM HT (Bcs.AdaptiveCommit.stopAt index (SHAOracle.route domain outside body) seen) =
      ((Observer.run (SHAOracle.merge domain outside HM) HT
          (Bcs.AdaptiveCommit.stopAt index body seen)).1,
        (Observer.run (SHAOracle.merge domain outside HM) HT
          (Bcs.AdaptiveCommit.stopAt index body seen)).2.filter (keep domain)) := by
  rw [← stop]
  exact run domain outside _ HM HT

end LfzkV2.Current.SHARouting
