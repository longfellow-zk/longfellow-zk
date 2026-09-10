import quadcert.Gen.Rung1.Rung1ArtifactPacked

/-! The artifact-owned part of Rung1, obtained only by reducing the verified LFC3 decoder. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Quadcert.Gen.Rung1Artifact

open Quadcert.Lfc2

def decoded : DecodedCircuit :=
  match decode p256 packedInput with
  | .ok circuit => circuit
  | .error _ =>
      { fieldId := 0
        ninput := 0
        npublicInput := 0
        noutput := 0
        logv := 0
        subfieldBoundary := 0
        constants := #[]
        layers := []
        legacyCircuitId := 0 }

/-- Kernel-checked success: `decoded` is not a fallback value. -/
theorem decode_ok : decode p256 packedInput = .ok decoded := by
  rfl

end Quadcert.Gen.Rung1Artifact
