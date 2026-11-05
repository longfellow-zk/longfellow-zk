import LfzkV2.Linear.Tests.Terminal
import LfzkV2.Linear.Runtime.ProfiledSide
import LfzkV2.Linear.Runtime.RawRuntimeExtraction
import Lean.Util.CollectAxioms

/-! Audit the new protocol endpoints independently of the retained checkpoint. -/

open Lean Elab Command

run_cmd do
  for endpoint in #[
      ``SumcheckV2.LinearTerminal.Data.bad_nonzero_roots,
      ``SumcheckV2.LinearTerminal.affine_layer_reduction,
      ``SumcheckV2.LinearTerminal.maskingEquiv,
      ``LfzkV2.Linear.buildConstraints_correct,
      ``LfzkV2.Linear.compiled_iff_clear,
      ``LfzkV2.Linear.Circuit.compiled_circuit_reduction,
      ``LfzkV2.Linear.Circuit.prove_complete,
      ``LfzkV2.Linear.Backend.satisfies_iff,
      ``LfzkV2.Linear.Packed.rows_frontend_or_bad,
      ``LfzkV2.Linear.Replay.semanticData_eq_of_prefix,
      ``LfzkV2.Linear.Replay.pointData_eq,
      ``LfzkV2.Linear.FiatShamir.Setup.normalized_soundness_le,
      ``LfzkV2.Linear.Runtime.Compiled.side,
      ``LfzkV2.Linear.Runtime.Direct.side,
      ``LfzkV2.Linear.Runtime.Compiled.profiledSide_profiled,
      ``LfzkV2.Linear.Runtime.Direct.profiledSide_profiled,
      ``LfzkV2.Linear.Runtime.TwoFieldPotential.extract_valid,
      ``LfzkV2.Linear.Runtime.TwoFieldCommitmentFS.extraction_le,
      ``LfzkV2.Linear.Runtime.RawExtraction.probability_le,
      ``LfzkV2.Linear.Runtime.RuntimeCost.error_le,
      ``LfzkV2.Linear.Runtime.RawRuntimeExtraction.probability_bound,
      ``LfzkV2.Linear.Runtime.RawRuntimeExtraction.extraction_116,
      ``LfzkV2.Linear.Replay.proofElements_eq,
      ``LfzkV2.Linear.Replay.padElements_eq] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
