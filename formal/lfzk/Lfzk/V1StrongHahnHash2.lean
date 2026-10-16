import Lfzk.V1StrongHahnData
import CodingTheory.ListDecoding.HahnDelsarte

/-! Checked Hahn endpoints for v7 hash geometry 2. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongHahnHash2

open Lfzk.V1StrongHahnData CodingTheory

theorem responseValid :
    HahnDelsarte.certificateValid 3318 1735 946 Hash2Response = true := by
  native_decide

theorem responseBound :
    HahnDelsarte.certifiedBound 3318 1735 Hash2Response =
      296750042811368 := by
  native_decide

theorem maskValid :
    HahnDelsarte.certificateValid 3318 1718 947 Hash2Mask = true := by
  native_decide

theorem maskBound :
    HahnDelsarte.certifiedBound 3318 1718 Hash2Mask =
      32172073361340530533752 := by
  native_decide

end Lfzk.V1StrongHahnHash2
