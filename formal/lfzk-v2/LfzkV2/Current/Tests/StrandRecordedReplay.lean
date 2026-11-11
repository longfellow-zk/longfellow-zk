import LfzkV2.Current.StrandRecordedReplay
import LfzkV2.Current.StrandMerkleDomains

/-! Axiom audit for original-table replay and its actual runtime bridge.
These equalities require no hash-output injectivity or query-order premise. -/
namespace LfzkV2.Current.Tests.StrandRecordedReplay

#print axioms Merkle.QueryTable.answer_of_mem
#print axioms Replay.Transcript.replay_congr_on_prefix
#print axioms StrandRecordedReplay.point_eq
#print axioms StrandRecordedReplay.read_eq
#print axioms StrandRecordedReplay.runtimeRead_eq
#print axioms StrandRecordedReplay.runtimeRead_off
#print axioms StrandMerkleDomains.input_ne_leaf
#print axioms StrandMerkleDomains.input_ne_node

end LfzkV2.Current.Tests.StrandRecordedReplay
