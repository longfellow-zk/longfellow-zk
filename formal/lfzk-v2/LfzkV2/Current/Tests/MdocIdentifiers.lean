import LfzkV2.Current.MdocIdentifiers

/-! Byte vectors for the current participant contexts. In particular each
geometry word is an unframed little-endian u64, and the joint participant
count follows both ordered field contexts. -/
namespace LfzkV2.Current.MdocIdentifiers.Tests
open TranscriptV2.Framing (encodeLE)

example : ((contextBytes [] 3).drop
    ((CanonicalPrefix.utf8 "polygero/root/context/linear/v1").length+8)) =
    [3,0,0,0,0,0,0,0, 93,1,0,0,0,0,0,0, 12,0,0,0,0,0,0,0,
      139,9,0,0,0,0,0,0, 84,0,0,0,0,0,0,0] := by decide +kernel

example : ((jointContextBytes (fun _ => 17) (fun _ => 34)).drop
    ((CanonicalPrefix.utf8 "polygero/joint/context/v1").length+80)) =
    [2,0,0,0,0,0,0,0] := by decide +kernel

example : ((jointContextBytes (fun _ => 17) (fun _ => 34)).drop
    (CanonicalPrefix.utf8 "polygero/joint/context/v1").length).take 9 =
    [16,0,0,0,0,0,0,0,17] := by decide +kernel

-- The statement message's tag and protocol value: the first 56 payload
-- bytes of node 0 of the 1-attribute mdoc vector (Rust commit 4).
example : statementHead =
    [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 108, 111, 110, 103, 102, 101, 108,
      108, 111, 119, 47, 118, 50, 47, 109, 100, 111, 99, 47, 116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47,
      118, 50] := by decide +kernel

#print axioms setup

end LfzkV2.Current.MdocIdentifiers.Tests
