import LfzkV2.Linear.TerminalSampling
import LfzkV2.ChallengeBlocks

/-! Ordinary challenge blocks keep their existing semantics. The terminal
adds a distinct nonzero challenge type, so a sampler cannot silently charge
its quadratic root bound against the full-field denominator. -/

namespace LfzkV2.Linear.Challenges

open SumcheckV2 Finset
open scoped Classical

variable {F C : Type} [Field F]

inductive Kind where
  | ordinary (block : ChallengeBlocks.Kind)
  | terminal
  deriving DecidableEq

abbrev Sample (F : Type) [Field F] : Kind → Type
  | .ordinary block => block.Sample F
  | .terminal => TerminalSampling.Nonzero F

abbrev Data (F : Type) [Field F] : Kind → Type
  | .ordinary block => ChallengeBlocks.Data F block
  | .terminal => LinearTerminal.Data F

def Data.Valid {kind : Kind} : Data F kind → Prop :=
  match kind with
  | .ordinary _ => ChallengeBlocks.Data.Valid
  | .terminal => fun _ => True

def Data.Bad {kind : Kind} : Data F kind → Sample F kind → Prop :=
  match kind with
  | .ordinary _ => ChallengeBlocks.Data.Bad
  | .terminal => fun data scale => LinearTerminal.Data.Bad data scale.val

end LfzkV2.Linear.Challenges
