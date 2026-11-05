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

abbrev Sampler (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C] : Kind → Type
  | .ordinary block => ChallengeBlocks.Sampler F C block
  | .terminal => TerminalSampling.Sampler F C

def Sampler.decode [Fintype F] [DecidableEq F] [Fintype C] {kind : Kind} :
    Sampler F C kind → C → Sample F kind :=
  match kind with
  | .ordinary _ => ChallengeBlocks.Sampler.decode
  | .terminal => TerminalSampling.Sampler.decode

def Kind.rawBudget (fieldFiber nonzeroFiber : ℕ) : Kind → ℕ
  | .ordinary block => fieldFiber * block.budget
  | .terminal => nonzeroFiber * 2

theorem Sampler.bad_card_le [Fintype F] [DecidableEq F] [Fintype C]
    {kind : Kind} (sampler : Sampler F C kind) (fieldFiber nonzeroFiber : ℕ)
    (hfield : fieldFiber * Fintype.card F = Fintype.card C)
    (hterminal : ∀ hs : kind = .terminal, (hs ▸ sampler).fiber = nonzeroFiber)
    (data : Data F kind) (hvalid : data.Valid) :
    (univ.filter fun answer => data.Bad (sampler.decode answer)).card ≤
      kind.rawBudget fieldFiber nonzeroFiber := by
  cases kind with
  | ordinary block => exact sampler.raw_bad_card fieldFiber hfield data hvalid
  | terminal =>
      have h := TerminalSampling.Sampler.bad_card_le sampler (fun _ : Unit => data)
      simpa [Kind.rawBudget, Data.Bad, Sampler.decode, hterminal rfl] using h

end LfzkV2.Linear.Challenges
