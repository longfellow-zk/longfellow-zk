import Lfzk.LigeroV1RowsV7
import Lfzk.V1StrongHahnHash1
import Lfzk.V1StrongHahnHash2
import Lfzk.V1StrongHahnHash3
import Lfzk.V1StrongHahnHash4

/-! Candidate extraction parameters for the stronger graded V1 v7 analysis. -/

set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Rows

open Lfzk.LigeroV1Rows Lfzk.V1StrongHahnData

def hash1 : Row :=
  { v7Hash1 with certificate :=
      { v7Hash1.certificate with
        e := 1543, g := 16, m := 1200474, targetBits := 0,
        maskThreshold := 1671, hahnMask := Hash1Mask } }

def hash2 : Row :=
  { v7Hash2 with certificate :=
      { v7Hash2.certificate with
        e := 1583, g := 17, m := 164862, targetBits := 0,
        maskThreshold := 1718, hahnMask := Hash2Mask } }

def hash3 : Row :=
  { v7Hash3 with certificate :=
      { v7Hash3.certificate with
        e := 1601, g := 16, m := 310355, targetBits := 0,
        maskThreshold := 1735, hahnMask := Hash3Mask } }

def hash4 : Row :=
  { v7Hash4 with certificate :=
      { v7Hash4.certificate with
        e := 1640, g := 17, m := 145658, targetBits := 0,
        maskThreshold := 1779, hahnMask := Hash4Mask } }

theorem hash1_listBound : hash1.listBound = 2 := by native_decide
theorem hash2_listBound : hash2.listBound = 2 := by native_decide
theorem hash3_listBound : hash3.listBound = 2 := by native_decide
theorem hash4_listBound : hash4.listBound = 2 := by native_decide

theorem hash1_valid : hash1.Valid := by native_decide
theorem hash2_valid : hash2.Valid := by native_decide
theorem hash3_valid : hash3.Valid := by native_decide
theorem hash4_valid : hash4.Valid := by native_decide


end Lfzk.V1StrongV7Rows
