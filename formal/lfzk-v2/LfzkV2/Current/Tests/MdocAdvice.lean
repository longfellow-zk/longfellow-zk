import LfzkV2.Current.MdocAdvice

namespace LfzkV2.Current.MdocAdvice.Tests

example : codec.encode ⟨0,by decide⟩ = [0,0,0] := by decide
example : codec.encode ⟨2^20-1,by decide⟩ = [255,255,15] := by decide
example : codec.decode [255,255,15] = some (⟨2^20-1,by decide⟩,[]) := by decide
example : codec.decode [0,0,16] = none := by decide
example : codec.decode [0,0] = none := by decide
example : codec.decode [1,4,0,123] = some (⟨1025,by decide⟩,[123]) := by decide

-- The second tree starts within the second byte, rather than at a byte boundary.
example : bits ⟨1024,by decide⟩ 0 9 = false := by decide
example : bits ⟨1024,by decide⟩ 1 0 = true := by decide
example : bits ⟨2^19,by decide⟩ 1 9 = true := by decide
example : decode ⟨0,by decide⟩ = some (fun _ _ => false) := by decide

end LfzkV2.Current.MdocAdvice.Tests
