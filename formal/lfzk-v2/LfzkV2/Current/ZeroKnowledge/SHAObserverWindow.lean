import LfzkV2.Current.SHAOracle
import LfzkV2.Current.ZeroKnowledge.ObserverWindow

/-! A single finite Merkle-domain marginal of the original SHA observer.
Complementary SHA values are fixed before this marginal is sampled. They
answer public identifier hashes and the observer's matching raw queries.
Both original mixed traces remain in the returned values. The public prior
and later query budgets are unchanged and therefore conservative. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.SHAObserverWindow
open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

variable {Raw D QT AT Request Proof Observed Salt Leaf : Type}
variable [Fintype D] [Fintype AT] [DecidableEq Raw]
variable [Fintype Request] [Fintype Proof] [Fintype Salt] [Fintype Leaf]
variable {preM preT postM postT : ℕ}
variable (domain : Raw → Prop) (outside : Raw → D)
variable (codec : Codec Salt Leaf D Raw)
variable (prior : TwoOracleTree Raw D QT AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree Raw D QT AT Observed postM postT)
local notation "Trace" => List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))

def Results : ObserverWindow.Index Request Proof → Type
  | .inl _ => Request × Trace
  | .inr _ => Observed × Trace

def trees : (index : ObserverWindow.Index Request Proof) →
    TwoOracleTree Raw D QT AT (Results (Raw := Raw) (D := D) (QT := QT) (AT := AT) (Observed := Observed) index)
      (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).1
      (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).2
  | .inl _ => SHAOracle.observer domain outside prior
  | .inr pair => SHAOracle.observer domain outside (after pair.1 pair.2)

def window : Finset Raw := MerkleOracleWindow.window codec _ (trees domain outside prior after)

theorem window_domain (leaf : ∀ value, domain (codec.leafEnc value))
    (node : ∀ children, domain (codec.nodeEnc children)) :
    ∀ query ∈ window domain outside codec prior after, domain query := by
  intro query member
  simp only [window,MerkleOracleWindow.window,mem_union,mem_image,mem_univ,true_and,mem_biUnion] at member
  rcases member with (⟨value,rfl⟩ | ⟨children,rfl⟩) | ⟨index,member⟩
  · exact leaf value
  · exact node children
  · cases index with
    | inl value => exact SHAOracle.queries_route_domain domain outside (Observer.record [] prior) query member
    | inr pair => exact SHAOracle.queries_route_domain domain outside (Observer.record [] (after pair.1 pair.2)) query member

theorem extend_outside (leaf : ∀ value, domain (codec.leafEnc value))
    (node : ∀ children, domain (codec.nodeEnc children))
    (HM : {raw // raw ∈ window domain outside codec prior after} → D)
    (query : Raw) (notDomain : ¬domain query) :
    OracleWindow.extend (window domain outside codec prior after) HM outside query = outside query := by
  have absent : query ∉ window domain outside codec prior after :=
    fun member => notDomain (window_domain domain outside codec prior after leaf node query member)
  exact dif_neg absent

theorem merge_extend (leaf : ∀ value, domain (codec.leafEnc value))
    (node : ∀ children, domain (codec.nodeEnc children))
    (HM : {raw // raw ∈ window domain outside codec prior after} → D) :
    SHAOracle.merge domain outside (OracleWindow.extend (window domain outside codec prior after) HM outside) =
      OracleWindow.extend (window domain outside codec prior after) HM outside := by
  funext query
  by_cases member : domain query
  · exact SHAOracle.merge_inside domain outside _ query member
  · rw [SHAOracle.merge_outside domain outside _ query member,
      extend_outside domain outside codec prior after leaf node HM query member]

def later (request : Request) (proof : Proof) (HT : QT → AT) :=
  (MerkleOracleWindow.finiteResidual codec _ (trees domain outside prior after) (.inr (request,proof)) HT).map Prod.fst

end LfzkV2.Current.ZeroKnowledge.SHAObserverWindow
