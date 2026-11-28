import LfzkV2
import LfzkV2.APITest
import LfzkV2.Current.Tests.APITest
import LfzkV1
import LfzkV1.AnnotationBudget125
import LfzkV1.CanonicalField125
import LfzkV1.CanonicalHashPrefix125
import LfzkV1.CanonicalOpening125
import LfzkV1.CanonicalSecondary125
import LfzkV1.HashCut125
import LfzkV1.HashFieldCharge125
import LfzkV1.HashFieldPoint125
import LfzkV1.HashFieldPath125
import LfzkV1.HashOpening125
import LfzkV1.HashReplayView125
import LfzkV1.LigeroHighMass125V7
import LfzkV1.LigeroOrder125
import LfzkV1.MacCharge125
import LfzkV1.MerkleWork125Total
import LfzkV1.MerkleWork125V7
import LfzkV1.RawProofAnnotation125
import LfzkV1.ReplayDecode125
import LfzkV1.ReplayFieldTape125
import LfzkV1.ReplayView125
import LfzkV1.ResidualReplay125Ligero
import LfzkV1.ResidualReplay125Profile
import LfzkV1.ResidualReplay125Run
import LfzkV1.SignatureBudget125
import LfzkV1.SoundnessBudget125
import LfzkV1.SoundnessCompose125
import LfzkV1.TwoFieldCover125
import LfzkV1.V7SamplerAudit125
import LfzkV1.V7Soundness125
import LfzkV1.V7Soundness125Instance
import LfzkV1.V7ZkProfile
import LfzkV1.V7ZkProfileInstance
import Survival
import Survival.Tests
import Survival.Axioms
import Bcs
import Merkle
import ECDSA
import PkCircuit
import CodingTheory
import ReedSolomon
import AffineAgreement
import SelectedMCA
import LigeroFamily
import Ligero
import Ligero.APITest
import Ligero.V1
import Ligero.V1.AdaptiveLocal
import LigeroLocalCounts
import JBAgreement
import SumcheckV1
import examples
import examples.Ligero
import polygero.Algebra
import polygero.Benchmarks.HahnRateSixteenth
import polygero.FiatShamir.Potential
import polygero.Local
import polygero.Protocol
import polygero.Recursion
import polygero.Reduction
import SumcheckV2.APITest
import DualPacking
import WitnessSelection.APITest
import TranscriptV2.APITest
import RuntimeHahn.APITest
import PolygeroRustHahn
import TunedProfiles
import MdocJointProfile
import polygero.APITest
import Bcs.FirstPairCombined
import Bcs.FirstPairPath
import Bcs.FirstPairQuery
import Bcs.FixedPathCommit
import Bcs.PotentialCommit
import Bcs.QueryRoleCompiler
import Bcs.TerminalPairTape
import Bcs.TwoCoordinatePotential
import Bcs.TwoFreshCoordinates
import Bcs.WeightedTerminal
import Lean.Util.CollectAxioms
import Lean.Util.Path

/-! Full declaration audit, including private helpers. This is a separate
audit command; the default build checks the public endpoints and certificates.
Legacy V1 numerical rows retain their documented native-evaluation trust.

It audits every module of this package it imports, and `formal/scripts/audit.rs`
checks that its imports reach every tracked Lean source. A module is this
package's when its object file is in the package's build directory, the one
holding `LfzkV2`'s; Lean's and the required packages' are elsewhere. -/

open Lean Elab Command

set_option maxHeartbeats 20000000

run_cmd do
  let env ← getEnv
  -- `moduleNames` maps the complete import array. Cache it before visiting
  -- declarations so ownership checks do not rebuild it for every constant.
  let moduleNames := env.header.moduleNames
  let some library := (← findOLean `LfzkV2).parent
    | throwError "cannot locate this package's build directory"
  let libraryPrefix := library.toString ++ System.FilePath.pathSeparator.toString
  let mut audited : NameSet := {}
  for mod in moduleNames do
    if (← findOLean mod).toString.startsWith libraryPrefix then
      audited := audited.insert mod
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
    unless audited.contains moduleName do continue
    let legacy := moduleName == `LfzkV1 || moduleName.toString.startsWith "LfzkV1." ||
      moduleName.toString.startsWith "examples.Ligero.Longfellow."
    if info.isAxiom && !(legacy && nativeFact name) then
      throwError "Unexpected axiom declaration: {name}"
    for ax in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax ||
          (legacy && nativeFact ax) do
        throwError "Unexpected axiom {ax} in {name} (module {moduleName})"
    if legacy then legacyCount := legacyCount + 1
    else strictCount := strictCount + 1
  logInfo m!"Audited the {audited.size} modules of this package: {strictCount} declarations with standard axioms only and {legacyCount} legacy V1 declarations with the documented native-row allowance."
