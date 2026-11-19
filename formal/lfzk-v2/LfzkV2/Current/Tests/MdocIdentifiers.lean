import LfzkV2.Current.MdocIdentifiers

/-! Byte vectors of the current mdoc setup. -/
namespace LfzkV2.Current.MdocIdentifiers.Tests
open TranscriptV2.Framing (encodeLE)

-- The statement message's tag and protocol value: the first 56 payload
-- bytes of node 0 of the four-slot NEXT mdoc vector.
example : statementHead =
    [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 108, 111, 110, 103, 102, 101, 108,
      108, 111, 119, 47, 118, 50, 47, 109, 100, 111, 99, 47, 116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47,
      118, 50] := by decide +kernel

-- A `Circuit` message: tag 18, then `Bytes(32)` (kind 0, length 32, the
-- identifier).
example : circuitMessage (fun _ => 7) =
    [18,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 32,0,0,0,0,0,0,0] ++ List.replicate 32 7 := by
  decide +kernel

#print axioms setup

end LfzkV2.Current.MdocIdentifiers.Tests
