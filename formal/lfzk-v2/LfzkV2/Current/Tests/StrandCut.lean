import LfzkV2.Current.StrandCut

namespace LfzkV2.Current.Tests.StrandCut
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling

private def program : Tree (StrandSearch.Name (Fin 3) Bool) (Sample Digest Word) Unit 4 :=
  .query (.inl (0,none)) fun _ =>
    .query (.inr (0,fun _ => 0)) fun _ =>
      .query (.inl (1,some true)) fun _ =>
        .query (.inl (2,none)) fun _ => .done ()

-- Neither an early PRF row's unused digest nor a hash queried after the
-- context was named can enter the commitment extractor's prefix.
example (H : StrandSearch.Name (Fin 3) Bool → Sample Digest Word) :
    StrandCut.trace id program H true = [(0,(H (.inl (0,none))).1)] := by
  simp [StrandCut.trace,program,beforeLabel,StrandCut.label]
  rfl

/--
info: 'LfzkV2.Current.StrandCut.trace_off' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandCut.trace_off

/--
info: 'LfzkV2.Current.StrandCut.trace_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandCut.trace_raw

end LfzkV2.Current.Tests.StrandCut
