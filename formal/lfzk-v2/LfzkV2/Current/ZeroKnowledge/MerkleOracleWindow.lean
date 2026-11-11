import LfzkV2.Current.ObserverWindow
import Merkle.Commit
import Merkle.CheckPass

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

theorem leaf_mem (value : Salt × Leaf) : codec.leafEnc value ∈ window codec budget trees :=
  mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_univ value)))

theorem node_mem (children : D × D) : codec.nodeEnc children ∈ window codec budget trees :=
  mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_univ children)))

theorem queries_subset (index : Index) : mixedQueries (trees index) ⊆ window codec budget trees := by
  intro raw member
  exact mem_union_right _ (mem_biUnion.mpr ⟨index,mem_univ _,member⟩)

def finiteCodec : Codec Salt Leaf D {raw // raw ∈ window codec budget trees} where
  leafEnc value := ⟨codec.leafEnc value,leaf_mem codec budget trees value⟩
  nodeEnc children := ⟨codec.nodeEnc children,node_mem codec budget trees children⟩

theorem finite_leaf_hash (HM : {raw // raw ∈ window codec budget trees} → D)
    (outside : Raw → D) (value : Salt × Leaf) :
    HM ((finiteCodec codec budget trees).leafEnc value) =
      OracleWindow.extend (window codec budget trees) HM outside (codec.leafEnc value) :=
  (OracleWindow.extend_mem (window codec budget trees) HM outside (codec.leafEnc value)
    (leaf_mem codec budget trees value)).symm

theorem finite_node_hash (HM : {raw // raw ∈ window codec budget trees} → D)
    (outside : Raw → D) (children : D × D) :
    HM ((finiteCodec codec budget trees).nodeEnc children) =
      OracleWindow.extend (window codec budget trees) HM outside (codec.nodeEnc children) :=
  (OracleWindow.extend_mem (window codec budget trees) HM outside (codec.nodeEnc children)
    (node_mem codec budget trees children)).symm

theorem finiteCodec_inj (injective : codec.Inj) : (finiteCodec codec budget trees).Inj :=
  ⟨fun _ _ equal => injective.leaf (congrArg Subtype.val equal),
    fun _ _ equal => injective.node (congrArg Subtype.val equal)⟩

def finiteTree (index : Index) :=
  restrictMixed (window codec budget trees) (trees index) (queries_subset codec budget trees index)

theorem finiteTree_run (index : Index)
    (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D) (HT : QT → AT) :
    ((Observer.run HM HT (finiteTree codec budget trees index)).1,
      (Observer.run HM HT (finiteTree codec budget trees index)).2.map (liftEvent (window codec budget trees))) =
      Observer.run (OracleWindow.extend (window codec budget trees) HM outside) HT (trees index) :=
  restrictMixed_extend_run (window codec budget trees) (trees index) (queries_subset codec budget trees index) HM outside HT

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

variable [Inhabited D]

/-- Every honest hash input is in the same finite marginal. Thus restricting
the codec and oracle changes no root or frontier label, on every branch and
without a commitment-injectivity assumption. -/
theorem commitLabels_eq (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D)
    (n : ℕ) (nonce : Fin n → Salt) (columns : Fin n → Leaf) (vertex : ℕ) :
    commitLabels ((finiteCodec codec budget trees).withOracle HM) n nonce columns vertex =
      commitLabels (codec.withOracle (OracleWindow.extend (window codec budget trees) HM outside)) n nonce columns vertex := by
  conv_lhs => rw [commitLabels]
  conv_rhs => rw [commitLabels]
  split_ifs with leaf internal
  · simp only [Codec.withOracle,finiteCodec,OracleWindow.extend,
      dif_pos (leaf_mem codec budget trees _)]
  · rw [commitLabels_eq HM outside n nonce columns (2*vertex),
      commitLabels_eq HM outside n nonce columns (2*vertex+1)]
    simp only [Codec.withOracle,finiteCodec,OracleWindow.extend,
      dif_pos (node_mem codec budget trees _)]
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem root_eq (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D)
    (n : ℕ) (nonce : Fin n → Salt) (columns : Fin n → Leaf) :
    root ((finiteCodec codec budget trees).withOracle HM) n nonce columns =
      root (codec.withOracle (OracleWindow.extend (window codec budget trees) HM outside)) n nonce columns :=
  commitLabels_eq codec budget trees HM outside n nonce columns 1

/-- The bounded honest commitment traversal has the identical heap and
full raw trace. This also applies when the finite oracle is a prepared or
otherwise changed table returned by a hybrid. -/
theorem commitPass_run (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D)
    (n : ℕ) (nonce : Fin n → Salt) (columns : Fin n → Leaf) (count : ℕ) (values : ℕ → D) :
    (((Merkle.MH.commitPass (finiteCodec codec budget trees) n nonce columns count values).run HM).1,
      ((Merkle.MH.commitPass (finiteCodec codec budget trees) n nonce columns count values).run HM).2.map
        (fun qa => (qa.1.val,qa.2))) =
      (Merkle.MH.commitPass codec n nonce columns count values).run
        (OracleWindow.extend (window codec budget trees) HM outside) := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      by_cases leaf : n ≤ count+1 ∧ count+1 < 2*n
      · simp only [Merkle.MH.commitPass,dif_pos leaf,Tree.run_query,finiteCodec,List.map_cons,
          OracleWindow.extend,dif_pos (leaf_mem codec budget trees _)]
        have tail := ih (Function.update values (count+1)
          (HM ⟨codec.leafEnc (nonce ⟨count+1-n,by omega⟩,columns ⟨count+1-n,by omega⟩),
            leaf_mem codec budget trees _⟩))
        have output := congrArg Prod.fst tail
        have trace := congrArg Prod.snd tail
        exact Prod.ext output (congrArg (List.cons _) trace)
      · by_cases internal : 0 < count+1 ∧ count+1 < n
        · simp only [Merkle.MH.commitPass,dif_neg leaf,dif_pos internal,Tree.run_query,finiteCodec,List.map_cons,
            OracleWindow.extend,dif_pos (node_mem codec budget trees _)]
          have tail := ih (Function.update values (count+1)
            (HM ⟨codec.nodeEnc (values (2*(count+1)),values (2*(count+1)+1)),node_mem codec budget trees _⟩))
          have output := congrArg Prod.fst tail
          have trace := congrArg Prod.snd tail
          exact Prod.ext output (congrArg (List.cons _) trace)
        · simpa only [Merkle.MH.commitPass,dif_neg leaf,dif_neg internal,Tree.run_weaken] using
            ih (Function.update values (count+1) default)

theorem openCore_eq (HM : {raw // raw ∈ window codec budget trees} → D) (outside : Raw → D)
    (n : ℕ) (I : Finset (Fin n)) (nonce : Fin n → Salt) (columns : Fin n → Leaf) :
    openCore ((finiteCodec codec budget trees).withOracle HM) n I nonce columns =
      openCore (codec.withOracle (OracleWindow.extend (window codec budget trees) HM outside)) n I nonce columns := by
  apply congrArg₂ Opening.mk rfl
  funext vertex
  exact commitLabels_eq codec budget trees HM outside n nonce columns vertex.val

end Codec
end LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow
