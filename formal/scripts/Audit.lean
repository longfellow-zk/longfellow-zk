import LfzkV2
import LfzkV2.Current.Tests.APITest
import LfzkV2.Joint.Tests.APITest
import LfzkV2.Layered.Tests.APITest
import LfzkV1
import LfzkV1.FlatV7All
import SumcheckV2.APITest
import DualPacking
import WitnessSelection.APITest
import TranscriptV2.APITest
import RuntimeHahn.APITest
import PolygeroRustHahn
import TunedProfiles
import polygero.APITest
import Bcs.FirstPairCharge
import Bcs.FirstPairCombined
import Bcs.FirstPairLocalContext
import Bcs.FirstPairPath
import Bcs.FirstPairQuery
import Bcs.QueryRoleCompiler
import Bcs.TerminalPairTape
import Bcs.TwoCoordinatePotential
import Bcs.TwoFreshCoordinates
import Bcs.WeightedTerminal
import Lean.Util.CollectAxioms

/-! Full declaration audit, including private helpers. This is a separate
audit command; the default build checks the public endpoints and certificates.
Legacy V1 numerical rows retain their documented native-evaluation trust. -/

open Lean Elab Command

set_option maxHeartbeats 20000000

private def auditedModule (name : Name) : Bool :=
  #["LfzkV1", "LfzkV2", "SumcheckV1", "SumcheckV2", "DualPacking", "WitnessSelection",
    "TranscriptV2", "Bcs", "Merkle",
    "polygero", "RuntimeHahn", "PolygeroRustHahn", "TunedProfiles"].any fun root =>
      name.toString == root || name.toString.startsWith (root ++ ".")

run_cmd do
  let env ← getEnv
  -- `moduleNames` maps the complete import array. Cache it before visiting
  -- declarations so ownership checks do not rebuild it for every constant.
  let moduleNames := env.header.moduleNames
  let owner := fun name => match env.getModuleIdxFor? name with
    | some idx => moduleNames[idx.toNat]!
    | none => env.mainModule
  let nativeFact := fun ax => ax == ``Lean.ofReduceBool ||
    ((owner ax).toString.startsWith "LfzkV1." ||
      (owner ax).toString.startsWith "examples.Ligero.Longfellow.") &&
      ax.toString.contains "._native.native_decide.ax_"
  let mut strictCount := 0
  let mut legacyCount := 0
  for (name, info) in env.constants do
    let moduleName := owner name
    unless auditedModule moduleName do continue
    let legacy := moduleName == `LfzkV1 || moduleName.toString.startsWith "LfzkV1."
    if info.isAxiom && !(legacy && nativeFact name) then
      throwError "Unexpected axiom declaration: {name}"
    for ax in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax ||
          (legacy && nativeFact ax) do
        throwError "Unexpected axiom {ax} in {name} (module {moduleName})"
    if legacy then legacyCount := legacyCount + 1
    else strictCount := strictCount + 1
  logInfo m!"Audited {strictCount} declarations with standard axioms only and {legacyCount} legacy V1 declarations with the documented native-row allowance."
