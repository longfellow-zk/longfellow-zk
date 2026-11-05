import LfzkV2.Joint.Tests.Structure
import LfzkV2.Joint.Honest
import LfzkV2.Joint.RawRuntimeExtraction
import Lean.Util.CollectAxioms

/-! Audit the joint checkpoint without altering the prior endpoints. -/

open Lean Elab Command

run_cmd do
  for endpoint in #[
      ``LfzkV2.Joint.Family.compiler_verify,
      ``LfzkV2.Joint.Family.verify_of_extraction,
      ``LfzkV2.Joint.Family.candidates_card,
      ``LfzkV2.Joint.Family.queryCharge_sum_le,
      ``LfzkV2.Joint.Family.backend_path_ge_one,
      ``LfzkV2.Joint.Honest.payload_verifies,
      ``LfzkV2.Joint.Honest.family_verifies,
      ``LfzkV2.Joint.Honest.compiled_complete,
      ``LfzkV2.Joint.Replay.backend_response_irrel,
      ``LfzkV2.Joint.Replay.statements_fixed,
      ``LfzkV2.Joint.Replay.responses_fixed,
      ``LfzkV2.Joint.Replay.preparedProof_coherent,
      ``LfzkV2.Joint.Charges.charge_sum_le,
      ``LfzkV2.Joint.Extraction.extract_valid,
      ``LfzkV2.Joint.Extraction.path_charge_ge_one,
      ``LfzkV2.Joint.FiatShamir.extraction_le,
      ``LfzkV2.Joint.Pair.accepts_of_extraction,
      ``LfzkV2.Joint.Commitment.extraction_le,
      ``LfzkV2.Joint.RawExtraction.probability_le,
      ``LfzkV2.Joint.Cost.sum_slotBudget,
      ``LfzkV2.Joint.RuntimeCost.error_le,
      ``LfzkV2.Joint.RawRuntimeExtraction.probability_bound,
      ``LfzkV2.Joint.RawRuntimeExtraction.extraction_116] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
