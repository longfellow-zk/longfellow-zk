import LfzkV2.Current.OracleWindow

/-! One raw-query window for a prior observer and every later continuation.
Only the prior program's finite output support is enumerated. Its private
state type may be infinite; no converted observer state is introduced. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandObserverWindow
open Merkle.RandomOracle
open scoped Classical

variable {Raw Digest Context Proof Observed : Type} [Fintype Digest] [DecidableEq Raw]

def outputs : {fuel : ℕ} → Tree Raw Digest Context fuel → Finset Context
  | _, .done context => {context}
  | _, .query _ next => Finset.univ.biUnion fun answer => outputs (next answer)

omit [DecidableEq Raw] in
theorem output_mem {fuel : ℕ} (before : Tree Raw Digest Context fuel) (H : Raw → Digest) :
    (before.run H).1 ∈ outputs before := by
  induction before with
  | done context => exact Finset.mem_singleton_self context
  | query raw next ih => exact Finset.mem_biUnion.mpr ⟨H raw,Finset.mem_univ _,ih (H raw)⟩

variable [Fintype Proof] {preFuel postFuel : ℕ}
variable (before : Tree Raw Digest Context preFuel)
variable (after : Context → Proof → Tree Raw Digest Observed postFuel)

def window : Finset Raw :=
  OracleWindow.queries before ∪ (outputs before).biUnion fun context =>
    Finset.univ.biUnion fun proof => OracleWindow.queries (after context proof)

theorem before_subset : OracleWindow.queries before ⊆ window before after := Finset.subset_union_left

theorem after_subset (context : Context) (reachable : context ∈ outputs before) (proof : Proof) :
    OracleWindow.queries (after context proof) ⊆ window before after := by
  intro raw member
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨context,reachable,
    Finset.mem_biUnion.mpr ⟨proof,Finset.mem_univ _,member⟩⟩)

theorem before_congr (H G : Raw → Digest) (same : ∀ raw ∈ window before after, H raw = G raw) :
    before.run H = before.run G := by
  apply Tree.run_congr_on_trace
  intro entry member
  exact (same entry.1 (before_subset before after (OracleWindow.trace_mem_queries before G entry member))).trans
    (Tree.trace_sound before G entry member).symm

theorem after_congr (context : Context) (reachable : context ∈ outputs before) (proof : Proof)
    (H G : Raw → Digest) (same : ∀ raw ∈ window before after, H raw = G raw) :
    (after context proof).run H = (after context proof).run G := by
  apply Tree.run_congr_on_trace
  intro entry member
  exact (same entry.1 (after_subset before after context reachable proof
    (OracleWindow.trace_mem_queries (after context proof) G entry member))).trans
    (Tree.trace_sound (after context proof) G entry member).symm

end LfzkV2.Current.ZeroKnowledge.StrandObserverWindow
