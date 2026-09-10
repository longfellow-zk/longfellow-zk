import quadcert.Bridge.Sha256Gf2.Gf2BoolMap

/-! Booleanity edges `1024 … 1535`, matched against `tnBool`. -/

set_option maxRecDepth 8000000
set_option maxHeartbeats 0

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

theorem ec2 : edgesMatchAt nodeFn tnBool mapOfB 1024 512 = true := by decide +kernel

end Sha256Gf2
