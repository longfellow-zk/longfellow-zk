import quadcert.Bridge.Sha256Gf2.Gf2BoolMap

/-! Booleanity edges `2048 … 2559`, matched against `tnBool`. -/

set_option maxRecDepth 8000000
set_option maxHeartbeats 0

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

theorem ec4 : edgesMatchAt nodeFn tnBool mapOfB 2048 512 = true := by decide +kernel

end Sha256Gf2
