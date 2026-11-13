import LfzkV2.Current.MdocAdvice

namespace LfzkV2.Current.MdocAdvice.Tests

-- Two separately encoded `MaskedWord<10>`, each two little-endian bytes.
example : codec.encode ![0,0] = [0,0,0,0] := by decide
example : codec.encode ![⟨2^10-1,by decide⟩,⟨1,by decide⟩] = [255,3,1,0] := by decide
example : codec.decode [255,3,1,0] = some (![⟨2^10-1,by decide⟩,⟨1,by decide⟩],[]) := by decide
-- Any nonzero padding bit in either word is rejected.
example : codec.decode [0,4,0,0] = none := by decide
example : codec.decode [0,0,0,128] = none := by decide
example : codec.decode [0,0,0] = none := by decide
example : codec.decode [1,2,3,1,123] = some (![⟨513,by decide⟩,⟨259,by decide⟩],[123]) := by decide

-- Each tree's word starts at its own byte boundary.
example : bits ![⟨512,by decide⟩,0] 0 9 = true := by decide
example : bits ![⟨512,by decide⟩,0] 1 0 = false := by decide
example : bits ![0,⟨1,by decide⟩] 1 0 = true := by decide
example : decode ![0,0] = some (fun _ _ => false) := by decide

-- The transcript writes the domain label, then one framed write per word.
example : writes.encode ![⟨2^10-1,by decide⟩,⟨1,by decide⟩] =
    [0,2,0,0,0,0,0,0,0,255,3] ++ [0,2,0,0,0,0,0,0,0,1,0] := by decide

end LfzkV2.Current.MdocAdvice.Tests
