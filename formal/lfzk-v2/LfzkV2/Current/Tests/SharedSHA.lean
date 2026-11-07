import LfzkV2.Current.MdocSharedSHASoundness

/-! Auxiliary SHA calls and repeated transcript inputs can be interleaved
with Merkle work. Domain projection must preserve the original boundary and
discard auxiliary preimages even when their digest equals a Merkle digest. -/
noncomputable section
namespace LfzkV2.Current.Tests.SharedSHA
open Merkle.RandomOracle ZeroKnowledge

def domain (query : ℕ) : Prop := query = 1
def outside (_query : ℕ) : Bool := false
def inside (_query : ℕ) : Bool := false
def transcript (_query : ℕ) : Bool := true

def prover : TwoOracleTree ℕ Bool ℕ Bool Bool 3 3 :=
  .queryLeft 0 fun _ => .queryLeft 1 fun _ =>
    .queryRight 17 fun _ => .queryLeft 0 fun _ =>
      .queryRight 17 fun _ => .queryRight 23 fun answer => .done answer

example : Observer.transcriptTrace (Observer.run inside transcript
    (SHAOracle.route domain outside prover)).2 = [(17,true),(17,true),(23,true)] := by
  rw [SHARouting.transcript_run]
  simp [prover,Observer.run,Observer.transcriptTrace,transcript,SHAOracle.merge,domain,outside,inside]

example : Observer.merkleTrace (Observer.run inside transcript
    (Bcs.AdaptiveCommit.stopAt 0 (SHAOracle.route domain outside prover) [])).2 = [(1,false)] := by
  rw [SHARouting.cut_run]
  simp [prover,Bcs.AdaptiveCommit.stopAt,Observer.run,Observer.merkleTrace,
    SHARouting.keep,SHAOracle.merge,domain,outside,inside]

example : Observer.transcriptTrace (Observer.run inside transcript
    (Bcs.AdaptiveCommit.stopAt 1 (SHAOracle.route domain outside prover) [])).2 = [(17,true),(17,true)] := by
  rw [SHARouting.cut_run,SHARouting.transcript_filter]
  simp [prover,Bcs.AdaptiveCommit.stopAt,Observer.run,Observer.transcriptTrace,
    SHAOracle.merge,domain,outside,inside,transcript]

example : (Observer.merkleTrace (Observer.run (SHAOracle.merge domain outside inside)
    transcript (Bcs.AdaptiveCommit.stopAt 0 prover [])).2).head? = some (0,false) := by
  simp [prover,Bcs.AdaptiveCommit.stopAt,Observer.run,Observer.merkleTrace,
    SHAOracle.merge,domain,outside,inside]

/-- A hand with no transcript calls needs no dummy inhabitant of the
challenge alphabet, even when the other oracle is still queried. -/
def noTranscript : TwoOracleTree ℕ Bool Empty Empty Bool 1 0 :=
  .queryLeft 0 fun answer => .done answer

example (tape : Fin 1 → Bool) :
    (lazyRun tape false (TranscriptV2.Memoize.left (Empty.elim : Empty → Empty) noTranscript) []).1 =
      ((TwoOracleTree.fixLeft tape false noTranscript []).run Empty.elim).1 :=
  SHALazy.lazy_output Empty.elim tape false noTranscript []

#check @MdocSharedSHASoundness.ratio_le
#print axioms SHARouting.cut_run
#print axioms SHALazy.setup_cut_run
#print axioms MdocSHAExperiment.original_output
#print axioms MdocSHAExperiment.cut_preserved
#print axioms MdocSHAExperiment.verify_merge
#print axioms MdocSHAExperiment.event_iff
#print axioms MdocSharedSHASoundness.ratio_le

end LfzkV2.Current.Tests.SharedSHA
