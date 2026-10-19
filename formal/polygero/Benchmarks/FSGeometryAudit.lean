import polygero.Benchmarks.FSBaselineAware81
import polygero.Benchmarks.FSGrindingInstance

/-! The common 81/80 geometry is inhabited, with an actual recursive
coefficient packing. This is not a compiled LFZK circuit instantiation. -/
namespace RecursivePolygero.Benchmarks.FSGeometryAudit
open FSGrindingInstance FiatShamir.TwoLevel

theorem inhabited_geometry :
    FSTwoLevel.Geometry concreteRetunedParent FSDefect81.parent ∧
    FSTwoLevel.Geometry concreteRetunedChild.instance FSDefect81.childRow := by
  constructor <;> constructor <;> rfl

end RecursivePolygero.Benchmarks.FSGeometryAudit
