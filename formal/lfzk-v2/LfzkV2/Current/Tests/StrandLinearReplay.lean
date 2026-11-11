import LfzkV2.Current.StrandSealIndependence
import Merkle.Indexed.Extraction

/-! Audit the bridge from the actual runtime encoder to numbered linear
replay, and the indexed Merkle extraction component used alongside it. -/
namespace LfzkV2.Current.Tests.StrandLinearReplay

#print axioms LfzkV2.Current.StrandLinearReplay.history_replay
#print axioms StrandSealIndependence.runtime_history_replay
#print axioms Merkle.Indexed.messages_agree

end LfzkV2.Current.Tests.StrandLinearReplay
