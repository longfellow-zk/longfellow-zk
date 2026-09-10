import quadcert.Bridge.Sha256Gf2.Gf2BoolMap

/-! Booleanity edges `4608 … 5119`, matched against `tnBool`. -/

set_option maxRecDepth 8000000
set_option maxHeartbeats 0

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

theorem ec9 : edgesMatchAt nodeFn tnBool mapOfB 4608 512 = true := by decide +kernel

end Sha256Gf2
