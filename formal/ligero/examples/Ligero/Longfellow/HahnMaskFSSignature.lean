import examples.Ligero.Longfellow.HahnMaskFS.V7Range0
import examples.Ligero.Longfellow.HahnMaskFS.V7Range1
import examples.Ligero.Longfellow.HahnMaskFS.V7Range2
import examples.Ligero.Longfellow.HahnMaskFS.V7Range3
import examples.Ligero.Longfellow.HahnMaskFS.V7Range4
import examples.Ligero.Longfellow.HahnMaskFS.V7Range5
import examples.Ligero.Longfellow.HahnMaskFS.V7Range6
import examples.Ligero.Longfellow.HahnMaskFS.V7Range7
import examples.Ligero.Longfellow.HahnMaskFS.V8Range0
import examples.Ligero.Longfellow.HahnMaskFS.V8Range1
import examples.Ligero.Longfellow.HahnMaskFS.V8Range2
import examples.Ligero.Longfellow.HahnMaskFS.V8Range3
import examples.Ligero.Longfellow.HahnMaskFS.V8Range4
import examples.Ligero.Longfellow.HahnMaskFS.V8Range5
import examples.Ligero.Longfellow.HahnMaskFS.V8Range6
import examples.Ligero.Longfellow.HahnMaskFS.V8Range7

/-! Public adaptive-FS V1 signature Hahn certificates, assembled from independent radius checks. -/

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask

/-- Checked Delsarte inequalities for the v7 signature cutoff. -/
theorem v7SigFS_valid :
    CodingTheory.HahnDelsarte.certificateValid 3187 1626 909 v7SigFS = true := by
  refine CodingTheory.HahnDelsarte.certificateValid_of_ranges
    3187 1626 909 v7SigFS [(0, 114), (114, 228), (228, 342), (342, 456), (456, 570), (570, 684), (684, 798), (798, 910)] ?_ ?_ ?_
  · native_decide
  · intro t ht
    by_cases h0 : t < 114
    · exact ⟨(0, 114), by simp, by omega, h0⟩
    by_cases h1 : t < 228
    · exact ⟨(114, 228), by simp, by omega, h1⟩
    by_cases h2 : t < 342
    · exact ⟨(228, 342), by simp, by omega, h2⟩
    by_cases h3 : t < 456
    · exact ⟨(342, 456), by simp, by omega, h3⟩
    by_cases h4 : t < 570
    · exact ⟨(456, 570), by simp, by omega, h4⟩
    by_cases h5 : t < 684
    · exact ⟨(570, 684), by simp, by omega, h5⟩
    by_cases h6 : t < 798
    · exact ⟨(684, 798), by simp, by omega, h6⟩
    exact ⟨(798, 910), by simp, by omega, by omega⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exact v7Range0
    exact v7Range1
    exact v7Range2
    exact v7Range3
    exact v7Range4
    exact v7Range5
    exact v7Range6
    exact v7Range7

/-- Checked Delsarte inequalities for the v8 signature cutoff. -/
theorem v8SigFS_valid :
    CodingTheory.HahnDelsarte.certificateValid 3458 1768 987 v8SigFS = true := by
  refine CodingTheory.HahnDelsarte.certificateValid_of_ranges
    3458 1768 987 v8SigFS [(0, 124), (124, 248), (248, 372), (372, 496), (496, 620), (620, 744), (744, 868), (868, 988)] ?_ ?_ ?_
  · native_decide
  · intro t ht
    by_cases h0 : t < 124
    · exact ⟨(0, 124), by simp, by omega, h0⟩
    by_cases h1 : t < 248
    · exact ⟨(124, 248), by simp, by omega, h1⟩
    by_cases h2 : t < 372
    · exact ⟨(248, 372), by simp, by omega, h2⟩
    by_cases h3 : t < 496
    · exact ⟨(372, 496), by simp, by omega, h3⟩
    by_cases h4 : t < 620
    · exact ⟨(496, 620), by simp, by omega, h4⟩
    by_cases h5 : t < 744
    · exact ⟨(620, 744), by simp, by omega, h5⟩
    by_cases h6 : t < 868
    · exact ⟨(744, 868), by simp, by omega, h6⟩
    exact ⟨(868, 988), by simp, by omega, by omega⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exact v8Range0
    exact v8Range1
    exact v8Range2
    exact v8Range3
    exact v8Range4
    exact v8Range5
    exact v8Range6
    exact v8Range7

end Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask
