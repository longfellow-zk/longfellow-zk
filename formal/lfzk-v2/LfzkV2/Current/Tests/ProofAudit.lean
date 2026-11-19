import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Check axiom dependencies independently of pretty-printing and line width. -/
namespace LfzkV2.Current.Tests.ProofAudit
open Lean Elab Command

def standardAxioms (declarations : Array Name) : CommandElabM Unit := do
  for declaration in declarations do
    unless (← getEnv).contains declaration do
      throwError "Missing audited declaration {declaration}"
    for axiomName in ← collectAxioms declaration do
      unless #[``propext,``Classical.choice,``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"

end LfzkV2.Current.Tests.ProofAudit
