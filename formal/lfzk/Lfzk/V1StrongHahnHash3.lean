import Lfzk.V1StrongHahnData
import CodingTheory.ListDecoding.HahnDelsarte

/-! Checked Hahn endpoints for v7 hash geometry 3. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongHahnHash3

open Lfzk.V1StrongHahnData CodingTheory

theorem responseValid :
    HahnDelsarte.certificateValid 3352 1751 954 Hash3Response = true := by
  native_decide

theorem responseBound :
    HahnDelsarte.certifiedBound 3352 1751 Hash3Response =
      385824707325065 := by
  native_decide

theorem maskValid :
    HahnDelsarte.certificateValid 3352 1735 955 Hash3Mask = true := by
  native_decide

theorem maskBound :
    HahnDelsarte.certifiedBound 3352 1735 Hash3Mask =
      21147756081366596998285 := by
  native_decide

end Lfzk.V1StrongHahnHash3
