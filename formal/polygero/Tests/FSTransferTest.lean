import polygero.Recursion.FSInputs
import polygero.Recursion.FSResponse
import polygero.Recursion.FSAmortization
import Bcs.EnvelopeReuse
import polygero.Recursion.FSListBound
import polygero.Local.MaskTranslation
import polygero.Local.WireReuse
import polygero.Instances.FSTwoLevel
import polygero.Recursion.FSLocalDomains
import polygero.Local.WeightedExceptions
import Lean.Util.CollectAxioms

/-! Boundary examples and an axiom audit for the new FS transfer. -/

namespace RecursivePolygero.FiatShamir.Tests

open Finset ProfileAnalysis
open scoped Classical

-- Small marginal frequencies cannot be used after adaptive label selection.
example (g : Fin 2) : mean (fun z : Fin 2 => indicator (z = g)) = 1 / 2 := by
  fin_cases g <;> norm_num [mean, indicator]

example : mean (fun z : Fin 2 => indicator (z = z)) = 1 := by
  simp [indicator]

-- Every family of at most two systems has total excess at most one.
example (T : Finset (Fin 3)) (hT : T.card ≤ 2) :
    ∑ _i ∈ T, max (0 : ℚ) (1 / 2 - 0) ≤ 1 := by
  have h : (T.card : ℚ) ≤ 2 := by exact_mod_cast hT
  simp only [sub_zero]
  norm_num [sum_const, nsmul_eq_mul]
  linarith

-- The corresponding full incidence is 3/2, while the desired transfer
-- at target rate one is one. A small-subfamily capacity certificate alone
-- cannot justify summing over every system.
example :
    mean (fun z : Unit => mean (SystemException.incidence (univ : Finset (Fin 3))
      (fun _ => (1 / 2 : ℚ)) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ : Unit => False) 0 z)) >
        profile 2 0 0 + (1 - profile 2 0 0) * 1 := by
  norm_num [mean, SystemException.incidence, indicator, profile]

-- The two-level recurrence includes the cross term, rather than a union sum.
example : twoError (1 / 4) (1 / 8) = (11 / 32 : ℚ) := by
  norm_num [twoError]

-- Two child commitments each obey the same marginal local bound.
-- Their whole-proof certificates nevertheless share a root load twice as
-- large. This refutes the implication between budget hypotheses, not FS
-- soundness of Polygero or the possibility of a better decomposition.
example :
    (∀ _v : Fin 2, (∑ _q : Unit, ∑ _r : Unit, (1 / 4 : ℚ)) ≤ 1 / 4) ∧
      TwoLevel.load (fun _ : TwoLevel.Candidate Unit (Fin 2) Unit Unit => (1 / 4 : ℚ))
        (TwoLevel.gamma ()) > 1 / 4 := by
  norm_num [TwoLevel.constant_load_gamma]

-- Challenge-wise injectivity does not identify a system from a response
-- hash input that omits the challenge. This is a boundary example for the
-- next first-hit proof, not a concrete Polygero collision or attack.
example (b : Bool) : Function.Injective (fun d : Bool => Bool.xor d b) := by
  cases b <;> decide

example : Bool.xor false false = Bool.xor true true := rfl

-- Capacity-weighted exceptional mass cannot replace a Boolean exception
-- cover. Even disjoint exceptional events lose probability when weighted.
example :
    mean (fun x : Fin 2 => ∑ d : Fin 2, (1 / 2 : ℚ) * indicator (x = d)) = 1 / 2 ∧
    mean (fun x : Fin 2 => indicator (∃ d : Fin 2, x = d)) = 1 := by
  norm_num [mean, indicator, Fin.sum_univ_succ]

end RecursivePolygero.FiatShamir.Tests

open Lean Elab Command

run_cmd do
  for name in #[
      ``RecursivePolygero.FiatShamir.TwoLevel.role_oracle_sound,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_oracle_sound,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound,
      ``RecursivePolygero.ProfileAnalysis.highSystems_capacity_sum_le,
      ``RecursivePolygero.ProfileAnalysis.weightedExceptions_mean_le,
      ``Bcs.TotalOracle.Footprint.selected_event_le,
      ``Bcs.TotalOracle.Footprint.event_le_expected_budget,
      ``Bcs.TotalOracle.Footprint.event_le_of_parent_charge,
      ``Bcs.TotalOracle.Footprint.selected_singleton_event_le,
      ``Bcs.TotalOracle.EnvelopeReuse.fixed_pair_mean,
      ``Bcs.TotalOracle.EnvelopeReuse.exceeds_no_loss,
      ``Bcs.TotalOracle.EnvelopeReuse.once_per_parent_insufficient,
      ``RecursivePolygero.SystemException.random_target_incidence_mean,
      ``RecursivePolygero.ProfileAnalysis.localIncidence_mean_of_hahn,
      ``RecursivePolygero.FiatShamir.seam_incidence_mean_le,
      ``RecursivePolygero.FiatShamir.twoLevel_incidence_mean_le,
      ``RecursivePolygero.FiatShamir.twoLevel_fs_transfer,
      ``RecursivePolygero.FiatShamir.twoLevel_fs_transfer_of_fanout,
      ``RecursivePolygero.FiatShamir.TwoLevel.accepts_iff,
      ``RecursivePolygero.FiatShamir.TwoLevel.failure_coverage,
      ``RecursivePolygero.FiatShamir.TwoLevel.local_average,
      ``RecursivePolygero.FiatShamir.TwoLevel.query_load_iff,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_finite_message_bound,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_no_loss_of_root_load,
      ``RecursivePolygero.FiatShamir.TwoLevel.parentPotential_local,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_no_loss_of_parent_charge,
      ``RecursivePolygero.ProfileAnalysis.highSystems_card_le,
      ``RecursivePolygero.ProfileAnalysis.high_target_list_cover,
      ``RecursivePolygero.FiatShamir.TwoLevel.failure_list_cover,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_bound,
      ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_loss_factor,
      ``RecursivePolygero.ProfileAnalysis.scanRecoverAt_translate,
      ``RecursivePolygero.ProfileAnalysis.translated_unmasked_wire_iff,
      ``RecursivePolygero.ProfileAnalysis.varyWireEntry_verify_iff,
      ``RecursivePolygero.ProfileAnalysis.query_avoids_mean,
      ``RecursivePolygero.FiatShamir.TwoLevel.varied_wire_query_count,
      ``RecursivePolygero.FiatShamir.TwoLevel.bad_varyWireEntry_of_false,
      ``RecursivePolygero.FiatShamir.TwoLevel.root_load_ge_wire_orbit,
      ``RecursivePolygero.Instances.FSTwoLevel.checked,
      ``RecursivePolygero.Instances.FSTwoLevel.fieldFloor_le_reference,
      ``RecursivePolygero.Instances.FSTwoLevel.certificate,
      ``RecursivePolygero.Instances.FSTwoLevel.certifiedFS,
      ``RecursivePolygero.Instances.FSTwoLevel.certifiedSoundness,
      ``RecursivePolygero.FiatShamir.TwoLevel.translated_query_count,
      ``RecursivePolygero.FiatShamir.TwoLevel.root_load_ge_mask_orbit,
      ``RecursivePolygero.ProfileAnalysis.large_response_assigned,
      ``RecursivePolygero.ProfileAnalysis.assigned_payload_unique,
      ``RecursivePolygero.ProfileAnalysis.full_response_excess_le_of_cover,
      ``RecursivePolygero.ProfileAnalysis.high_target_covered_or_proper,
      ``RecursivePolygero.ProfileAnalysis.properException_mean_le,
      ``RecursivePolygero.FiatShamir.twoLevel_fullResponse_mean_le,
      ``RecursivePolygero.FiatShamir.seam_properException_mean_le] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
