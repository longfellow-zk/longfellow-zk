import CodingTheory.ListDecoding.HahnDelsarteTable
import examples.Ligero.Longfellow.HahnMaskFSData

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Checked v8 Hahn certificate on radii [372, 496). -/
theorem v8Range3 :
    CodingTheory.HahnDelsarte.certificateRangeValid 3458 1768 372 496 v8SigFS = true := by
  have htable :
      CodingTheory.HahnDelsarte.certificateRangeTableValid
        3458 1768 372 496 v8SigFS = true := by native_decide
  simpa only [CodingTheory.HahnDelsarte.certificateRangeTableValid_eq] using htable

end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
