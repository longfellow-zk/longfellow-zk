import Lfzk.V1StrongHahnExtraData
import CodingTheory.ListDecoding.HahnDelsarte

/-! Closed checks for the sparse supplemental v7 V1 response endpoints. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongHahnExtras

open Lfzk.V1StrongHahnExtraData CodingTheory

theorem hash1Response2Valid :
    HahnDelsarte.certificateValid 3230 1700 920 Hash1Response2 = true := by
  native_decide

theorem hash1Response2Bound :
    HahnDelsarte.certifiedBound 3230 1700 Hash1Response2 =
      28849652485 := by
  native_decide

theorem hash2Response2Valid :
    HahnDelsarte.certificateValid 3318 1744 946 Hash2Response2 = true := by
  native_decide

theorem hash2Response2Bound :
    HahnDelsarte.certifiedBound 3318 1744 Hash2Response2 =
      198458899828 := by
  native_decide

theorem hash3Response2Valid :
    HahnDelsarte.certificateValid 3352 1764 954 Hash3Response2 = true := by
  native_decide

theorem hash3Response2Bound :
    HahnDelsarte.certifiedBound 3352 1764 Hash3Response2 =
      31273126198 := by
  native_decide

theorem hash4ResponseEarlyValid :
    HahnDelsarte.certificateValid 3436 1801 978 Hash4ResponseEarly = true := by
  native_decide

theorem hash4ResponseEarlyBound :
    HahnDelsarte.certifiedBound 3436 1801 Hash4ResponseEarly =
      10885581438852 := by
  native_decide

theorem hash4Response2Valid :
    HahnDelsarte.certificateValid 3436 1805 978 Hash4Response2 = true := by
  native_decide

theorem hash4Response2Bound :
    HahnDelsarte.certifiedBound 3436 1805 Hash4Response2 =
      220138078851 := by
  native_decide

theorem hash4ResponseLateValid :
    HahnDelsarte.certificateValid 3436 1809 978 Hash4ResponseLate = true := by
  native_decide

theorem hash4ResponseLateBound :
    HahnDelsarte.certifiedBound 3436 1809 Hash4ResponseLate =
      21488178000 := by
  native_decide

end Lfzk.V1StrongHahnExtras
