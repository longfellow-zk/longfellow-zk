import LfzkV2.Current.ObserverWindow
import LfzkV2.Current.Observer
import LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow

/-! Canonical transcript inputs can be used to execute an arbitrary raw
byte observer. Recording precedes decoding, so malformed and repeated raw
queries remain in its view. Inputs outside the canonical image read the
same complementary oracle slice in the honest and simulated experiments. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.TranscriptObserver
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical
variable {QM AM Point Raw AT Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)
variable (outside : Raw → AT) (HM : QM → AM) (HT : Point → AT)

section Queries
variable [Fintype AM] [Fintype AT] [DecidableEq QM]

private theorem weakenRight_queries {left right : ℕ}
    (tree : TwoOracleTree QM AM Point AT Out left right) :
    ObserverWindow.mixedQueries (weakenRight tree) = ObserverWindow.mixedQueries tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenRight,ObserverWindow.mixedQueries,ih]
  | queryRight query next ih => simp only [weakenRight,ObserverWindow.mixedQueries,ih]

/-- Decoding transcript inputs only removes locally answered transcript calls.
It adds no SHA input, so the original observer's finite SHA window still covers
every branch of the translated observer. -/
theorem program_queries {left right : ℕ} (tree : TwoOracleTree QM AM Raw AT Out left right) :
    ObserverWindow.mixedQueries (codec.program outside tree) ⊆ ObserverWindow.mixedQueries tree := by
  induction tree with
  | done value => exact Finset.empty_subset _
  | queryLeft query next ih =>
      simp only [ByteOracleTransport.Codec.program,ObserverWindow.mixedQueries]
      apply Finset.insert_subset_insert
      exact Finset.biUnion_mono fun answer _ => ih answer
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none =>
          simp only [ByteOracleTransport.Codec.program,decoded,weakenRight_queries]
          intro raw member
          exact Finset.mem_biUnion.mpr ⟨outside query,Finset.mem_univ _,ih (outside query) member⟩
      | some point =>
          simp only [ByteOracleTransport.Codec.program,decoded,ObserverWindow.mixedQueries]
          exact Finset.biUnion_mono fun answer _ => ih answer
end Queries

private theorem weakenRight_run {left right : ℕ}
    (tree : TwoOracleTree QM AM Point AT Out left right) :
    Observer.run HM HT (weakenRight tree) = Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenRight,Observer.run,ih]
  | queryRight query next ih => simp only [weakenRight,Observer.run,ih]

theorem program_output {left right : ℕ} (tree : TwoOracleTree QM AM Raw AT Out left right) :
    (Observer.run HM HT (codec.program outside tree)).1 =
      (Observer.run HM (codec.oracle outside HT) tree).1 := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [ByteOracleTransport.Codec.program,Observer.run,ih]
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none =>
          simp only [ByteOracleTransport.Codec.program,decoded,weakenRight_run,Observer.run,
            ByteOracleTransport.Codec.oracle,ih]
      | some point =>
          simp only [ByteOracleTransport.Codec.program,decoded,Observer.run,ByteOracleTransport.Codec.oracle,ih]

def observer {left right : ℕ} (tree : TwoOracleTree QM AM Raw AT Out left right) :=
  codec.program outside (Observer.record [] tree)

/-- The returned output contains every original raw query and answer,
including outside-image queries which no longer need a typed query node. -/
theorem observer_output {left right : ℕ} (tree : TwoOracleTree QM AM Raw AT Out left right) :
    (Observer.run HM HT (observer codec outside tree)).1 =
      Observer.run HM (codec.oracle outside HT) tree := by
  rw [observer,program_output,Observer.record_output]
  simp only [List.nil_append,Prod.eta]

/-- Programming one canonical point changes exactly its encoded raw input.
The decoder's second inverse law rules out alternative raw aliases. -/
theorem oracle_update [DecidableEq Point] [DecidableEq Raw]
    (point : {point // valid point}) (answer : AT) :
    codec.oracle outside (Function.update HT point.val answer) =
      Function.update (codec.oracle outside HT) (codec.encode point) answer := by
  funext raw
  by_cases same : raw = codec.encode point
  · subst raw
    simp only [ByteOracleTransport.Codec.oracle_encode,Function.update_self]
  · rw [Function.update_of_ne same]
    cases decoded : codec.decode raw with
    | none => simp only [ByteOracleTransport.Codec.oracle,decoded]
    | some decodedPoint =>
        have different : decodedPoint.val ≠ point.val := by
          intro equal
          have samePoint : decodedPoint = point := Subtype.ext equal
          exact same ((codec.encode_decode raw decodedPoint decoded).symm.trans
            (congrArg codec.encode samePoint))
        simp only [ByteOracleTransport.Codec.oracle,decoded,Function.update_of_ne different]

end LfzkV2.Current.ZeroKnowledge.TranscriptObserver
