import LfzkV2.Current.ObserverWindow

/-! A finite marginal for the Merkle oracle on arbitrary raw strings.
The window contains every codec image and every query on every branch of
the supplied bounded observers. It does not assert that the raw byte-string
type is finite. The second oracle, its answers and the full mixed traces
are preserved, including when a hybrid returns a changed transcript oracle. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow
open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

open LfzkV2.Current.ObserverWindow
variable {Raw D QT AT Value : Type}
variable [Fintype D] [Fintype AT] [DecidableEq Raw]

section Codec
variable {Salt Leaf Index : Type} [Fintype Salt] [Fintype Leaf] [Fintype Index]
variable {Results : Index → Type}
variable (codec : Codec Salt Leaf D Raw)
variable (budget : Index → ℕ × ℕ)
variable (trees : (index : Index) → TwoOracleTree Raw D QT AT (Results index) (budget index).1 (budget index).2)

def window : Finset Raw :=
  ((univ.image codec.leafEnc) ∪ (univ.image codec.nodeEnc)) ∪
    (univ.biUnion fun index => mixedQueries (trees index))

theorem queries_subset (index : Index) : mixedQueries (trees index) ⊆ window codec budget trees := by
  intro raw member
  exact mem_union_right _ (mem_biUnion.mpr ⟨index,mem_univ _,member⟩)

def finiteResidual (index : Index) (HT : QT → AT) :=
  OracleWindow.restrict (window codec budget trees) (Observer.fixTranscript HT (trees index))
    ((queries_fixTranscript_subset HT (trees index)).trans (queries_subset codec budget trees index))

/-- The value returned by the one-oracle residual is the entire original
mixed execution, including every repeated call to either oracle. -/
theorem finiteResidual_output (index : Index)
    (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D) (HT : QT → AT) :
    ((finiteResidual codec budget trees index HT).run HM).1 =
      Observer.run (OracleWindow.extend (window codec budget trees) HM outside) HT (trees index) := by
  have transport := congrArg Prod.fst (OracleWindow.restrict_extend_run
    (window codec budget trees) (Observer.fixTranscript HT (trees index))
    ((queries_fixTranscript_subset HT (trees index)).trans (queries_subset codec budget trees index)) HM outside)
  exact transport.trans (congrArg Prod.fst (Observer.fixTranscript_run HT
    (OracleWindow.extend (window codec budget trees) HM outside) (trees index)))

end Codec
end LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow
