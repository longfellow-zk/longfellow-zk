import LfzkV2.Layered.Tests.Structure
import LfzkV2.Layered.PackedProver
import LfzkV2.Layered.FrontendBound
import LfzkV2.Layered.Runtime.ProfiledSide
import LfzkV2.Layered.Joint.RawRuntimeExtraction
import LfzkV2.Layered.Joint.Causality
import LfzkV2.Joint.Honest
import Lean.Util.CollectAxioms

/-! Audit the layered frontend and its authenticated composition while
keeping the earlier checkpoint endpoints in the default build. -/

open Lean Elab Command

run_cmd do
  for endpoint in #[
      ``LfzkV2.Layered.Entry.dot_weights,
      ``LfzkV2.Layered.Entry.cancellation,
      ``LfzkV2.Layered.fragments_outputs,
      ``LfzkV2.Layered.term_left_kernel,
      ``LfzkV2.Layered.term_right_kernel,
      ``LfzkV2.Layered.sparseLayer_left,
      ``LfzkV2.Layered.sparseLayer_right,
      ``LfzkV2.Layered.transition_flatten,
      ``LfzkV2.Layered.Circuit.soundness_reduction,
      ``LfzkV2.Layered.Circuit.compiled_circuit_reduction,
      ``LfzkV2.Layered.Circuit.prove_complete,
      ``LfzkV2.Layered.Packed.rows_frontend_or_bad,
      ``LfzkV2.Layered.Packed.rows_soundness,
      ``LfzkV2.Layered.Packed.honest_rows,
      ``LfzkV2.Layered.Replay.semanticData_eq_of_prefix,
      ``LfzkV2.Layered.Replay.pointData_valid,
      ``LfzkV2.Layered.Replay.pointData_eq,
      ``LfzkV2.Layered.Replay.slots_le,
      ``LfzkV2.Layered.Replay.ordinaryBudget_le,
      ``LfzkV2.Layered.Replay.mdoc_hash_budget,
      ``LfzkV2.Layered.Replay.mdoc_signature_budget,
      ``LfzkV2.Layered.Runtime.Compiled.satisfies_frontend_or_bad,
      ``LfzkV2.Layered.Runtime.Direct.satisfies_frontend,
      ``LfzkV2.Layered.Runtime.Compiled.profiledSide_packingBudget,
      ``LfzkV2.Layered.Joint.Replay.backend_response_irrel,
      ``LfzkV2.Layered.Joint.Replay.statements_fixed,
      ``LfzkV2.Layered.Joint.Replay.responses_fixed,
      ``LfzkV2.Layered.Joint.Extraction.extract_valid,
      ``LfzkV2.Layered.Joint.FiatShamir.extraction_le,
      ``LfzkV2.Layered.Joint.RawExtraction.probability_le,
      ``LfzkV2.Layered.Joint.RawRuntimeExtraction.probability_bound,
      ``LfzkV2.Layered.Joint.RawRuntimeExtraction.extraction_116,
      ``LfzkV2.Joint.Honest.compiled_complete] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
