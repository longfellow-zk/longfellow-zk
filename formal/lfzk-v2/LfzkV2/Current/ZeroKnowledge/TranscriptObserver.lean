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

end LfzkV2.Current.ZeroKnowledge.TranscriptObserver
