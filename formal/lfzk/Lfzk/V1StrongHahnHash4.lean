import Lfzk.V1StrongHahnData
import CodingTheory.ListDecoding.HahnDelsarte

/-! Checked Hahn endpoints for v7 hash geometry 4. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongHahnHash4

open Lfzk.V1StrongHahnData CodingTheory

theorem responseValid :
    HahnDelsarte.certificateValid 3436 1796 978 Hash4Response = true := by
  native_decide

theorem responseBound :
    HahnDelsarte.certifiedBound 3436 1796 Hash4Response =
      308529467083846 := by
  native_decide

theorem maskValid :
    HahnDelsarte.certificateValid 3436 1779 979 Hash4Mask = true := by
  native_decide

theorem maskBound :
    HahnDelsarte.certifiedBound 3436 1779 Hash4Mask =
      29500986658266217788398 := by
  native_decide

end Lfzk.V1StrongHahnHash4
