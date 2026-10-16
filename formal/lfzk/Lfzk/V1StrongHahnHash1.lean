import Lfzk.V1StrongHahnData
import CodingTheory.ListDecoding.HahnDelsarte

/-! Checked Hahn endpoints for the first v7 hash geometry. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongHahnHash1

open Lfzk.V1StrongHahnData CodingTheory

theorem responseValid :
    HahnDelsarte.certificateValid 3230 1687 920 Hash1Response = true := by
  native_decide

theorem responseBound :
    HahnDelsarte.certifiedBound 3230 1687 Hash1Response =
      400966108258685 := by
  native_decide

theorem maskValid :
    HahnDelsarte.certificateValid 3230 1671 921 Hash1Mask = true := by
  native_decide

theorem maskBound :
    HahnDelsarte.certifiedBound 3230 1671 Hash1Mask =
      23685505588402463438815 := by
  native_decide

end Lfzk.V1StrongHahnHash1
