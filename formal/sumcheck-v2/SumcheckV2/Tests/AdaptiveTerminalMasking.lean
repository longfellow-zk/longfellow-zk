import SumcheckV2.AdaptiveTerminalMasking
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! The challenge really depends on the earlier message. Tests remain separate
from the masking proof and audit the exact three-message distribution. -/
namespace SumcheckV2.Tests.AdaptiveTerminalMasking
open SumcheckV2.LinearTerminal
open scoped Classical

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def scale (cross : ZMod 5) : {r : ZMod 5 // r ≠ 0} :=
  if h : cross = 0 then ⟨1,by decide⟩ else ⟨cross,h⟩

example (A B : ZMod 5) (messages : ZMod 5 × ZMod 5 × ZMod 5) :
    (Finset.univ.filter fun pads => adaptiveHonestMessages A B scale pads = messages).card = 1 :=
  by
    convert adaptive_uniform_fiber A B scale messages using 1
    congr 1
    ext pads
    simp

example (A B : ZMod 5) (messages : ZMod 5 × ZMod 5 × ZMod 5) :
    residual (A * B) messages.1 (scale messages.1).val messages.2.1 messages.2.2
      (honestPadCells (adaptiveRecoverPads A B scale messages)) = 0 :=
  adaptive_simulated_terminal A B scale messages

example (messages : ZMod 2 × ZMod 2 × ZMod 2) :
    (Finset.univ.filter fun pads =>
      adaptiveHonestMessages (1 : ZMod 2) 0 (fun _ => ⟨1,by decide⟩) pads = messages).card = 1 :=
  by
    convert adaptive_uniform_fiber (1 : ZMod 2) 0 (fun _ => ⟨1,by decide⟩) messages using 1
    congr 1
    ext pads
    simp

#print axioms adaptive_uniform_fiber
#print axioms adaptive_simulated_terminal
end SumcheckV2.Tests.AdaptiveTerminalMasking
