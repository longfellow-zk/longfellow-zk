import LfzkV2.Current.ZeroKnowledge.SHAObserverWindow
import LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
import LfzkV2.Current.ZeroKnowledge.TranscriptObserver

/-! A fixed SHA marginal covers all possible public contexts and all
branches of the original observer. Routing complementary inputs may choose
a smaller marginal depending on that complementary slice; it never adds a
query to this fixed window. Unused coordinates are averaged for free. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.SHAGlobalWindow
open Merkle Merkle.MH Merkle.RandomOracle Finset LigeroFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {Raw D QT AT Value Context Salt Leaf : Type}
variable [Fintype D] [Fintype AT] [DecidableEq Raw]

private theorem record_queries {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right)
    (past : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    ObserverWindow.mixedQueries (Observer.record past tree) = ObserverWindow.mixedQueries tree := by
  induction tree generalizing past with
  | done value => rfl
  | queryLeft query next ih => simp only [Observer.record,ObserverWindow.mixedQueries,ih]
  | queryRight query next ih => simp only [Observer.record,ObserverWindow.mixedQueries,ih]

theorem route_queries (domain : Raw → Prop) (outside : Raw → D)
    {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    ObserverWindow.mixedQueries (SHAOracle.route domain outside tree) ⊆ ObserverWindow.mixedQueries tree := by
  induction tree with
  | done value => exact empty_subset _
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [SHAOracle.route,if_pos member,ObserverWindow.mixedQueries]
        apply insert_subset_insert
        exact biUnion_mono fun answer _ => ih answer
      · simp only [SHAOracle.route,if_neg member,SHAOracle.queries_weakenLeft,ObserverWindow.mixedQueries]
        intro raw inside
        exact mem_insert_of_mem (mem_biUnion.mpr ⟨outside query,mem_univ _,ih (outside query) inside⟩)
  | queryRight query next ih =>
      simp only [SHAOracle.route,ObserverWindow.mixedQueries]
      exact biUnion_mono fun answer _ => ih answer

theorem observer_queries (domain : Raw → Prop) (outside : Raw → D)
    {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    ObserverWindow.mixedQueries (SHAOracle.observer domain outside tree) ⊆ ObserverWindow.mixedQueries tree := by
  exact (route_queries domain outside (Observer.record [] tree)).trans (record_queries tree []).subset

variable [Fintype Context] [Fintype Salt] [Fintype Leaf]
variable (codecs : Context → Codec Salt Leaf D Raw)

def window (queries : Finset Raw) : Finset Raw :=
  (univ.biUnion fun context => univ.image (codecs context).leafEnc ∪ univ.image (codecs context).nodeEnc) ∪ queries

theorem window_mono {first second : Finset Raw} (contains : first ⊆ second) :
    window codecs first ⊆ window codecs second := by
  intro raw member
  rcases mem_union.mp member with member | member
  · exact mem_union.mpr (Or.inl member)
  · exact mem_union.mpr (Or.inr (contains member))

theorem leaf_mem (queries : Finset Raw) (context : Context) (value : Salt × Leaf) :
    (codecs context).leafEnc value ∈ window codecs queries :=
  mem_union_left _ (mem_biUnion.mpr ⟨context,mem_univ _,mem_union_left _ (mem_image_of_mem _ (mem_univ value))⟩)

theorem node_mem (queries : Finset Raw) (context : Context) (value : D × D) :
    (codecs context).nodeEnc value ∈ window codecs queries :=
  mem_union_left _ (mem_biUnion.mpr ⟨context,mem_univ _,mem_union_right _ (mem_image_of_mem _ (mem_univ value))⟩)

variable {Request Proof Observed : Type} [Fintype Request] [Fintype Proof]
variable {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree Raw D QT AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree Raw D QT AT Observed postM postT)

def observerQueries : Finset Raw := ObserverWindow.mixedQueries prior ∪
  (univ.biUnion fun pair : Request × Proof => ObserverWindow.mixedQueries (after pair.1 pair.2))

theorem routed_window_subset (domain : Raw → Prop) (outside : Raw → D) (context : Context) :
    SHAObserverWindow.window domain outside (codecs context) prior after ⊆
      window codecs (observerQueries prior after) := by
  intro raw member
  simp only [SHAObserverWindow.window,MerkleOracleWindow.window,mem_union,mem_image,mem_univ,true_and,mem_biUnion] at member
  rcases member with (⟨value,rfl⟩ | ⟨children,rfl⟩) | ⟨index,member⟩
  · exact leaf_mem codecs (observerQueries prior after) context value
  · exact node_mem codecs (observerQueries prior after) context children
  · apply mem_union_right
    cases index with
    | inl value => exact mem_union_left _ (observer_queries domain outside prior member)
    | inr pair =>
        exact mem_union_right _ (mem_biUnion.mpr ⟨pair,mem_univ _,
          observer_queries domain outside (after pair.1 pair.2) member⟩)

section PublicFamily
variable {Public : Type} [Fintype Public] (queries : Public → Type)
variable (priorFamily : (visible : Public) → TwoOracleTree Raw D (queries visible) AT Request preM preT)
variable (afterFamily : (visible : Public) → Request → Proof →
  TwoOracleTree Raw D (queries visible) AT Observed postM postT)

/-- Public setup may determine the observer syntax and typed query space.
Its finite public values are included before an oracle slice is chosen. -/
def familyQueries : Finset Raw :=
  univ.biUnion fun visible => observerQueries (priorFamily visible) (afterFamily visible)

theorem routed_family_window_subset (domain : Raw → Prop) (outside : Raw → D)
    (visible : Public) (context : Context) :
    SHAObserverWindow.window domain outside (codecs context) (priorFamily visible) (afterFamily visible) ⊆
      window codecs (familyQueries queries priorFamily afterFamily) := by
  apply (routed_window_subset codecs (priorFamily visible) (afterFamily visible) domain outside context).trans
  apply window_mono
  intro raw member
  exact mem_biUnion.mpr ⟨visible,mem_univ _,member⟩

end PublicFamily

section TranscriptInputs
variable {Input Point : Type} {valid : Point → Prop}
variable (transcript : ByteOracleTransport.Codec Point Input valid) (complement : Input → AT)
variable (rawPrior : TwoOracleTree Raw D Input AT Request preM preT)
variable (rawAfter : Request → Proof → TwoOracleTree Raw D Input AT Observed postM postT)

theorem translated_observerQueries :
    observerQueries (transcript.program complement rawPrior)
        (fun request proof => transcript.program complement (rawAfter request proof)) ⊆
      observerQueries rawPrior rawAfter := by
  intro raw member
  rcases mem_union.mp member with member | member
  · exact mem_union_left _ (TranscriptObserver.program_queries transcript complement rawPrior member)
  · obtain ⟨pair,_,member⟩ := mem_biUnion.mp member
    exact mem_union_right _ (mem_biUnion.mpr ⟨pair,mem_univ _,
      TranscriptObserver.program_queries transcript complement (rawAfter pair.1 pair.2) member⟩)

/-- One window chosen from the original raw observer works for every public
transcript codec and its malformed-input complement. Its choice does not
depend on either oracle's answers. -/
theorem translated_window_subset (domain : Raw → Prop) (outside : Raw → D) (context : Context) :
    SHAObserverWindow.window domain outside (codecs context) (transcript.program complement rawPrior)
        (fun request proof => transcript.program complement (rawAfter request proof)) ⊆
      window codecs (observerQueries rawPrior rawAfter) := by
  apply (routed_window_subset codecs (transcript.program complement rawPrior)
    (fun request proof => transcript.program complement (rawAfter request proof)) domain outside context).trans
  exact window_mono codecs (translated_observerQueries transcript complement rawPrior rawAfter)

end TranscriptInputs

section Restriction
variable {R S View : Type} [Fintype R] [Fintype S]
variable (small large : Finset Raw) (contains : small ⊆ large)

/-- A bound for a smaller uniform table also holds after independently
sampling every unused coordinate of a fixed larger marginal. -/
theorem restriction_statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (real : R → ({raw // raw ∈ small} → D) → View)
    (simulate : S → ({raw // raw ∈ small} → D) → View)
    (law : StatClose epsilon (fun coin : R × ({raw // raw ∈ small} → D) => real coin.1 coin.2)
      (fun coin : S × ({raw // raw ∈ small} → D) => simulate coin.1 coin.2)) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ large} → D) => real coin.1 (fun raw => coin.2 ⟨raw.val,contains raw.property⟩))
      (fun coin : S × ({raw // raw ∈ large} → D) => simulate coin.1 (fun raw => coin.2 ⟨raw.val,contains raw.property⟩)) := by
  let e := SHAProbability.inclusionEquiv small large contains
  let f := fun r (H : {raw : {raw // raw ∈ large} // raw.val ∈ small} → D) => real r (fun raw => H (e raw))
  let g := fun s (H : {raw : {raw // raw ∈ large} // raw.val ∈ small} → D) => simulate s (fun raw => H (e raw))
  have each : StatClose epsilon
      (fun coin : R × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → D) => f coin.1 coin.2)
      (fun coin : S × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → D) => g coin.1 coin.2) := by
    apply statClose_reindex
      (Equiv.prodCongr (Equiv.refl R) (Equiv.arrowCongr e (Equiv.refl D)).symm)
      (Equiv.prodCongr (Equiv.refl S) (Equiv.arrowCongr e (Equiv.refl D)).symm) ?_ ?_ law
    · intro coin; rfl
    · intro coin; rfl
  let predicate := fun raw : {raw // raw ∈ large} => raw.val ∈ small
  let F := fun (_ : {raw : {raw // raw ∈ large} // ¬predicate raw} → D)
    (coin : R × ({raw : {raw // raw ∈ large} // predicate raw} → D)) => f coin.1 coin.2
  let G := fun (_ : {raw : {raw // raw ∈ large} // ¬predicate raw} → D)
    (coin : S × ({raw : {raw // raw ∈ large} // predicate raw} → D)) => g coin.1 coin.2
  have mixed := statClose_mix nonnegative F G (fun _ => each)
  apply statClose_reindex
    (SHAProbability.coinsEquiv (R := R) (Answer := D) predicate)
    (SHAProbability.coinsEquiv (R := S) (Answer := D) predicate) ?_ ?_ mixed
  · intro coin; rfl
  · intro coin; rfl

end Restriction
end LfzkV2.Current.ZeroKnowledge.SHAGlobalWindow
