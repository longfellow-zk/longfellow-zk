import LfzkV2.Current.StrandOriginalSeal
import LfzkV2.Current.ConcreteMetadata

namespace LfzkV2.Current.Tests.StrandOriginalSeal
open TranscriptV2 Merkle.RandomOracle Bcs.TotalOracle
open scoped Classical

-- The address depends on a node answer, but not on either PRF answer.
private def address (_ : Unit) (H : Fin 3 → Bool) : Fin 3 := if H 0 then 1 else 2
private def original : Tree (Fin 3) Bool Unit 0 := .done ()

private theorem independent (out : Unit) (H H' : Fin 3 → Bool)
    (agree : AgreeOff (address out H) H H') : address out H = address out H' := by
  have node : H 0 = H' 0 := agree 0 (by unfold address; split <;> decide)
  simp only [address,node]

example : Bcs.FiniteProbability.density
    (StrandSealCharging.UnqueriedSeal address (fun _ => false) original) ≤ 1 / 2 := by
  exact StrandSealCharging.unqueriedSeal_density_le address (fun _ => false) independent original

-- An empty original trace remains empty even if verifier replay reads the
-- very same address before checking the stored seal. Replay must not turn
-- a missing original query into a present one.
private def replay : Tree (Fin 3) Bool Bool 2 :=
  .query 0 fun node => .query (if node then 1 else 2) fun answer => .done answer

example (H : Fin 3 → Bool) : address () H ∈ seen replay H := by
  simp [address,replay,seen,queried,Tree.run_query,Tree.run_done]

example (H : Fin 3 → Bool) :
    StrandSealCharging.UnqueriedSeal address (fun _ => false) original H ↔
      H (address () H) = false := by
  simp [StrandSealCharging.UnqueriedSeal,original,seen,queried,Tree.run_done]

-- The protocol premise is already proved for the actual metadata encoder.
#guard_msgs (drop info) in #check ConcreteMetadata.metadata_challengeIndependent
#guard_msgs (drop info) in #check Replay.Encoding.replay_transcript

/--
info: 'LfzkV2.Current.StrandSealIndependence.finalSealAddress_off' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSealIndependence.finalSealAddress_off

/--
info: 'LfzkV2.Current.StrandOriginalSeal.original_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandOriginalSeal.original_ratio_le

/--
info: 'LfzkV2.Current.StrandOriginalSeal.accepted_original_ratio_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandOriginalSeal.accepted_original_ratio_le

/--
info: 'LfzkV2.Current.StrandOriginalSeal.concrete_original_ratio_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandOriginalSeal.concrete_original_ratio_le

end LfzkV2.Current.Tests.StrandOriginalSeal
