import LfzkV2.Current.ZeroKnowledge.ObserverSupport
import LfzkV2.Current.ByteOracleTransport

/-! One transcript-oracle marginal covers all canonical protocol inputs
and every branch of a stateful observer. Private contexts and raw query
strings need not form finite types: only the original prior tree's finite
output support is used to enumerate possible post-proof programs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.TranscriptGlobalWindow
open Merkle.RandomOracle Finset
open scoped Classical

variable {QueryM D Raw Answer Context Proof Out : Type}
variable [Fintype D] [Fintype Answer] [DecidableEq Raw]

def queries : {left right : ℕ} → TwoOracleTree QueryM D Raw Answer Out left right → Finset Raw
  | _,_,.done _ => ∅
  | _,_,.queryLeft _ next => univ.biUnion fun answer => queries (next answer)
  | _,_,.queryRight raw next => insert raw (univ.biUnion fun answer => queries (next answer))

variable [Fintype Proof] {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree QueryM D Raw Answer Context preM preT)
variable (after : Context → Proof → TwoOracleTree QueryM D Raw Answer Out postM postT)

def observerQueries : Finset Raw :=
  queries prior ∪ ((ObserverSupport.outputs prior).biUnion fun context =>
    univ.biUnion fun proof => queries (after context proof))

theorem prior_subset : queries prior ⊆ observerQueries prior after := subset_union_left

theorem after_subset (HM : QueryM → D) (HT : Raw → Answer) (proof : Proof) :
    queries (after (Observer.run HM HT prior).1 proof) ⊆ observerQueries prior after := by
  intro raw member
  exact mem_union_right _ (mem_biUnion.mpr ⟨_,ObserverSupport.run_mem HM HT prior,
    mem_biUnion.mpr ⟨proof,mem_univ _,member⟩⟩)

section PublicFamily
variable {Public : Type} [Fintype Public]
variable (Point : Public → Type) [∀ visible, Fintype (Point visible)]
variable (valid : (visible : Public) → Point visible → Prop)
variable (codecs : (visible : Public) → ByteOracleTransport.Codec (Point visible) Raw (valid visible))
variable (priorFamily : Public → TwoOracleTree QueryM D Raw Answer Context preM preT)
variable (afterFamily : Public → Context → Proof → TwoOracleTree QueryM D Raw Answer Out postM postT)

@[irreducible] def window : Finset Raw :=
  (univ.biUnion fun visible => univ.image (codecs visible).encode) ∪
    (univ.biUnion fun visible => observerQueries (priorFamily visible) (afterFamily visible))

theorem canonical_mem (visible : Public) (point : {point // valid visible point}) :
    (codecs visible).encode point ∈ window Point valid codecs priorFamily afterFamily := by
  rw [window]
  exact mem_union_left _ (mem_biUnion.mpr ⟨visible,mem_univ _,mem_image_of_mem _ (mem_univ point)⟩)

theorem observer_subset (visible : Public) :
    observerQueries (priorFamily visible) (afterFamily visible) ⊆ window Point valid codecs priorFamily afterFamily := by
  intro raw member
  rw [window]
  exact mem_union_right _ (mem_biUnion.mpr ⟨visible,mem_univ _,member⟩)

end PublicFamily
end LfzkV2.Current.ZeroKnowledge.TranscriptGlobalWindow
