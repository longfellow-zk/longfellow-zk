import LfzkV2.Current.ByteCodecs
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Literal wire checks for raw proof-body primitives. Count words, field
values and transcript-operation tags are distinct layers of serialization. -/
namespace LfzkV2.Current.Tests.ByteCodecs
open PrefixCodec

def word : PrefixCodec (Fin 65536) := unsigned 2 65536 (by decide)

example : word.encode 4660 = [52,18] := by decide
example : word.decode [52,18,255] = some (4660,[255]) := by decide
example : word.decode [52] = none := by decide

def smallWord : PrefixCodec (Fin 251) := unsigned 1 251 (by decide)
example : smallWord.decode [251,0] = none := by decide
example : smallWord.decode [250,0] = some (250,[0]) := by decide

example : (vector byte 3).encode ![1,2,3] = [1,2,3] := by decide
example : (vector byte 3).decode [1,2,3,4] = some (![1,2,3],[4]) := by decide

def frontier : PrefixCodec ((length : Fin 4) × (Fin length.val → TranscriptV2.Framing.Byte)) :=
  counted 1 4 (by decide) (fun length => Fin length.val → TranscriptV2.Framing.Byte)
    (fun length => vector byte length.val)

example : frontier.encode ⟨2,![7,9]⟩ = [2,7,9] := by decide
example : frontier.decode [4,7,9] = none := by decide
example : frontier.decode [2,7] = none := by decide
example : frontier.decode [0,99] = some (⟨0,Fin.elim0⟩,[99]) := by decide

example : ((marker [77,68,65,54]).pair word).encode ((),4660) = [77,68,65,54,52,18] := by decide
example : ((marker [77,68,65,54]).pair word).decode [77,68,65,53,52,18] = none := by decide

end LfzkV2.Current.Tests.ByteCodecs
