import Lfzk.LigeroV1RowsV7
import examples.Ligero.Longfellow.HahnMaskCertificates

/-!
# A Hahn/Delsarte row for the deployed v7 signature geometry

The protocol and opening count are unchanged. The mask certificate from the improved flat
Ligero analysis also certifies a round-by-round row: set both doom thresholds to one below its
first certified agreement. This is a fresh RBR calculation, not a substitution of the flat
IOP error into an RBR theorem. The hash certificates' much larger mask lists do not give the
same improvement over GF(2^128).
-/

namespace Lfzk.LigeroV1Rows

set_option maxHeartbeats 4000000

/-- The v7 signature geometry, with a certified mask range starting at 1665 instead of 1703. -/
def v7SigHahn : Row :=
  { certificate :=
      { n := 3187, k := 455, d := 2733, e := 1522, g := 0, m := 8726582,
        fieldBits := 256, fieldOrder := p256Order, targetBits := 126, openings := 132,
        maskThreshold := 1665,
        hahnMask := Ligero.Examples.Grid.LongfellowProfiledExtraction.HahnMask.v7Sig }
    failureThreshold := 1664, arithmeticThreshold := 1664 }

theorem v7SigHahn_valid : v7SigHahn.Valid := by native_decide
theorem v7SigHahn_sharp : v7SigHahn.Sharp := by native_decide
theorem v7SigHahn_listBound : v7SigHahn.listBound = 2 := by native_decide

/-- The geometry is exactly the existing signature row's; only the analysis changes. -/
theorem v7SigHahn_geometry :
    (v7SigHahn.n, v7SigHahn.k, v7SigHahn.openings, v7SigHahn.fieldSize) =
      (v7Sig.n, v7Sig.k, v7Sig.openings, v7Sig.fieldSize) := rfl

end Lfzk.LigeroV1Rows
