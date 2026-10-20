import polygero.Instances.FSStoppingAudit
import polygero.Instances.FSCoreData
namespace RecursivePolygero.Instances.FSCoreStoppingAudit
open Bcs.StoppedPotential
def capacity : ℚ := FSCoreData.baseline+FSCoreData.capacity 2912
def barrier : ℚ := 4*capacity/(FSTwoLevel.fieldSize*capacity+4)

/-- The explicit support-only relaxation needs more than 3.78 field units,
even though its exact baseline-aware upper certificate uses only 3.82. -/
theorem checked : (378/100 : ℚ)/FSTwoLevel.fieldSize < barrier ∧
    FSDefect81.sameIOPError < barrier := by
  simp only [barrier,capacity,FSCoreData.baseline,FSCoreData.capacity,
    FSDefectData.baseline,FSDefectData.capacity,FSStoppedSpectrum.theta,FSTwoLevel.fieldSize,
    FSDefect81.sameIOPError,FiatShamir.twoError,ProfileAnalysis.profile,FSTwoLevel.theta,
    FSDefect81.parent,FSWholeBlock81.parent,FSBaselinePrice.row,FSDefect81.childRow,
    FSWholeBlock81.childRow,FSIntegerAffine.childRow,FSTwoLevel.rankError,
    Nat.choose_eq_fast_choose]
  decide +kernel


end RecursivePolygero.Instances.FSCoreStoppingAudit
