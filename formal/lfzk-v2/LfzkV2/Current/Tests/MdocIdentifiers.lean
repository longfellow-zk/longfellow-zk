import LfzkV2.Current.MdocIdentifiers

/-! Byte vectors for the current participant contexts. In particular each
geometry word is an unframed little-endian u64, and the joint participant
count follows both ordered field contexts. -/
namespace LfzkV2.Current.MdocIdentifiers.Tests

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

#print axioms setup
#print axioms parameters

end LfzkV2.Current.MdocIdentifiers.Tests
