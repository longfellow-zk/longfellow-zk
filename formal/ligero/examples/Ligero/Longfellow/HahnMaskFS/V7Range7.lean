import CodingTheory.ListDecoding.HahnDelsarteTable
import examples.Ligero.Longfellow.HahnMaskFSData

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Checked v7 Hahn certificate on radii [798, 910). -/
theorem v7Range7 :
    CodingTheory.HahnDelsarte.certificateRangeValid 3187 1626 798 910 v7SigFS = true := by
  have htable :
      CodingTheory.HahnDelsarte.certificateRangeTableValid
        3187 1626 798 910 v7SigFS = true := by native_decide
  simpa only [CodingTheory.HahnDelsarte.certificateRangeTableValid_eq] using htable

end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
