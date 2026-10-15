import CodingTheory.ListDecoding.HahnDelsarteTable
import examples.Ligero.Longfellow.HahnMaskFSData

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Checked v7 Hahn certificate on radii [456, 570). -/
theorem v7Range4 :
    CodingTheory.HahnDelsarte.certificateRangeValid 3187 1626 456 570 v7SigFS = true := by
  have htable :
      CodingTheory.HahnDelsarte.certificateRangeTableValid
        3187 1626 456 570 v7SigFS = true := by native_decide
  simpa only [CodingTheory.HahnDelsarte.certificateRangeTableValid_eq] using htable

end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
