import quadcert.Bridge.Sha256Gf2.Gf2BoolMap

/-! Booleanity edges `3584 … 4095`, matched against `tnBool`. -/

set_option maxRecDepth 8000000
set_option maxHeartbeats 0

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

theorem ec7 : edgesMatchAt nodeFn tnBool mapOfB 3584 512 = true := by decide +kernel

end Sha256Gf2
