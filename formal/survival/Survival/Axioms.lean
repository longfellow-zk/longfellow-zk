import Survival.Tests
import Survival.CausalCharges
import Survival.QueryOrder
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Check every generic Survival declaration, including private helpers and
the transitive assumptions of imported lemmas. Application adapters are audited
by the current V2 API audit. -/
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => match env.getModuleIdxFor? name with
    | some index => modules[index.toNat]!
    | none => env.mainModule
  let mut checked := 0
  for (name, info) in env.constants do
    let moduleName := (owner name).toString
    unless moduleName == "Survival" || moduleName.startsWith "Survival." do continue
    if info.isAxiom then throwError "Unexpected axiom declaration: {name}"
    for ax in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    checked := checked+1
  logInfo m!"Audited {checked} generic Survival declarations: standard Lean axioms only."
