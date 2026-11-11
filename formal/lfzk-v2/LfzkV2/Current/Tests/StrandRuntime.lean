import LfzkV2.Current.StrandRuntime
import LfzkV2.Current.StrandSampling
import LfzkV2.Current.RuntimeAdaptiveReduction

namespace LfzkV2.Current.Tests.StrandRuntime
open Finset
open scoped Classical

private def rejection (coins : Fin 4) : Option (Fin 3) :=
  if accepted : coins.val < 3 then some ⟨coins.val,accepted⟩ else none

-- Mathematical failure padding never changes a successful runtime value;
-- only a failed read uses its independent dummy coordinate.
example (fallback : Fin 3) :
    TranscriptV2.StrandSampling.complete rejection (⟨2,by decide⟩,fallback) = ⟨2,by decide⟩ := rfl

example (fallback : Fin 3) :
    TranscriptV2.StrandSampling.complete rejection (⟨3,by decide⟩,fallback) = fallback := rfl

private noncomputable def component :=
  StrandSampling.componentEquiv (Coins := Option Bool) (Equiv.refl (Bool × Bool)) id 1 (fun value => by
    calc
      _ = ({some value} : Finset (Option Bool)).card := by
        congr 1
        ext coins
        simp only [mem_filter,mem_univ,true_and,id_eq,mem_singleton]
      _ = 1 := card_singleton _)

-- Filling the current round's factor preserves every unused role factor.
-- Failed physical reads use padding; successful reads keep their real value.
example : (component (some false,(true,true))).1 = (false,true) := by
  unfold component
  rw [StrandSampling.componentEquiv_apply]
  rfl

example : (component (none,(true,false))).1 = (true,false) := by
  unfold component
  rw [StrandSampling.componentEquiv_apply]
  rfl

example (raw : Option Bool) (padding : Bool × Bool) :
    component.symm (component (raw,padding)) = (raw,padding) := component.symm_apply_apply _

-- Independent analysis coordinates do not replace any raw answer. This
-- holds for a whole adaptive oracle, not just one field-sample marginal.
example (H : Bool → Bool × (Option Bool × (Bool × Bool))) :
    (StrandSampling.oracleEquiv (fun _ : Bool => component)).symm
      ((StrandSampling.oracleEquiv (fun _ : Bool => component)) H) = H :=
  (StrandSampling.oracleEquiv (fun _ : Bool => component)).symm_apply_apply H

-- Retaining a raw trace as output preserves rejected bytes and the exact
-- cut observation even when later queries depend on those bytes.
example {fuel : ℕ}
    (program : Merkle.RandomOracle.Tree Bool (Bool × (Option Bool × (Bool × Bool))) Bool fuel)
    (residual : Bool → Fin (Fintype.card (Option Bool))) (H : Bool → Bool × (Bool × Bool)) :
    ((StrandSampling.reindex (fun _ : Bool => component) residual
      (TranscriptV2.recordTrace program)).run H).1 =
        program.run ((StrandSampling.oracleEquiv (fun _ : Bool => component)).symm (H,residual)) := by
  simpa only [TranscriptV2.run_recordTrace] using
    (StrandSampling.reindex_run (fun _ : Bool => component) residual (TranscriptV2.recordTrace program) H).1

#guard_msgs (drop info) in #check StrandSampling.componentEquiv_success

/--
info: 'TranscriptV2.StrandSampling.complete_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandSampling.complete_fiber

/--
info: 'LfzkV2.Current.StrandRuntime.Runtime.toPoint_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRuntime.Runtime.toPoint_parent

/--
info: 'LfzkV2.Current.StrandSearch.searchState_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSearch.searchState_bind

/--
info: 'LfzkV2.Current.StrandRuntime.seal_required' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRuntime.seal_required

/--
info: 'LfzkV2.Current.StrandRuntime.Runtime.toPoint_history' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRuntime.Runtime.toPoint_history

#guard_msgs (drop info) in #check StrandRuntime.complete_body_node

/--
info: 'LfzkV2.Current.StrandRuntime.named_replay_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRuntime.named_replay_length

/--
info: 'LfzkV2.Current.RuntimeAdaptiveFS.decoded_charge_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms RuntimeAdaptiveFS.decoded_charge_cover

/--
info: 'LfzkV2.Current.StrandSampling.oracle_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSampling.oracle_law

#guard_msgs (drop info) in #check StrandSampling.componentEquiv_inverse_success
#guard_msgs (drop info) in #check StrandSampling.reindex_firstOfTwo

private def retry : Merkle.RandomOracle.Tree Bool (Option Bool) (Option Bool) 2 :=
  .query false fun first => match first with
    | some value => .done (some value)
    | none => .query true fun second => .done second

-- The second component is not sampled by this role. The successful retry
-- supplies its first component, while the rejected first block stays visible.
example : ((StrandSampling.read (Equiv.refl (Bool × Bool)) (false,false) retry).run
    (fun index => if index then some true else none)) =
      (some (true,false),[(false,none),(true,some true)]) := rfl

-- Independent padding cannot make an exhausted physical sampler succeed.
example : ((StrandSampling.read (Equiv.refl (Bool × Bool)) (true,true) retry).run
    (fun _ => none)).1 = none := rfl

/--
info: 'LfzkV2.Current.StrandSampling.read_inverse_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSampling.read_inverse_success

/--
info: 'LfzkV2.Current.StrandSampling.oracle_on_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSampling.oracle_on_success

end LfzkV2.Current.Tests.StrandRuntime
